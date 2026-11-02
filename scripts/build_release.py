#!/usr/bin/env python3
"""Build release payloads from Git objects, never from working-tree files."""
from __future__ import annotations
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import tarfile

PDF_PATH = 'frontier/negative-voting-simplex/output/pdf/negative_gaussian_simplex_stability_v2.pdf'
PDF_ASSET = 'negative_gaussian_simplex_stability_v2.pdf'
INTEGRATED_PATH = 'frontier/negative-voting-simplex/supplements/integrated-full-voting-proof-20261102/MAIN_THEOREM_INTEGRATED_PROOF_20261102.txt'
INTEGRATED_ASSET = 'negative_voting_integrated_proof_20261102.txt'
EXTRA_ASSETS = {
    'negative_voting_simplex_preprint.pdf': 'preprints/negative-voting-simplex/output/pdf/negative_voting_simplex_preprint.pdf',
    'negative-voting-simplex-arxiv-source-2026-11-02.tar.gz': 'archives/negative-voting-simplex-arxiv-source-2026-11-02.tar.gz',
    'negative-voting-lean-2026-11-02.tar.gz': 'archives/negative-voting-lean-2026-11-02.tar.gz',
}


def git(repo: Path, *args: str) -> bytes:
    return subprocess.check_output(['git', '-C', str(repo), *args])


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def snapshot(repo: Path, commit: str) -> dict[str, tuple[int, bytes]]:
    if not re.fullmatch(r'[0-9a-f]{40}|[0-9a-f]{64}', commit):
        raise ValueError('A full lowercase commit ID is required')
    actual = git(repo, 'rev-parse', '--verify', commit + '^{commit}').decode().strip()
    if actual != commit:
        raise ValueError('Commit identity changed during resolution')
    files = {}
    for record in git(repo, 'ls-tree', '-rz', '--full-tree', commit).split(b'\0'):
        if not record:
            continue
        meta, raw_path = record.split(b'\t', 1)
        mode, kind, blob = meta.decode().split()
        name = raw_path.decode('utf-8')
        path = PurePosixPath(name)
        if path.is_absolute() or '..' in path.parts or '\n' in name or '\r' in name:
            raise ValueError('Unsafe tracked path')
        if kind != 'blob' or mode not in ('100644', '100755'):
            raise ValueError(f'Only regular tracked files are supported: {name}')
        files[name] = (int(mode[-3:], 8), git(repo, 'cat-file', 'blob', blob))
    return files


def validate_manifest(files: dict[str, tuple[int, bytes]]) -> dict:
    manifest = json.loads(files['RELEASE_MANIFEST.json'][1])
    pins = manifest['files']
    if set(pins) != set(files) - {'RELEASE_MANIFEST.json'}:
        raise ValueError('Release manifest must cover every tracked file except itself')
    for name, expected in pins.items():
        if not re.fullmatch(r'[0-9a-f]{64}', expected) or sha256(files[name][1]) != expected:
            raise ValueError(f'Committed manifest mismatch: {name}')
    return manifest


def archive_bytes(files: dict[str, tuple[int, bytes]], prefix: str, epoch: int) -> bytes:
    tar_buffer = io.BytesIO()
    with tarfile.open(fileobj=tar_buffer, mode='w', format=tarfile.PAX_FORMAT) as tar:
        for name, (mode, content) in sorted(files.items()):
            info = tarfile.TarInfo(prefix + '/' + name)
            info.size, info.mode, info.mtime = len(content), mode, epoch
            info.uid = info.gid = 0
            info.uname = info.gname = ''
            tar.addfile(info, io.BytesIO(content))
    output = io.BytesIO()
    with gzip.GzipFile(fileobj=output, mode='wb', filename='', mtime=0, compresslevel=9) as stream:
        stream.write(tar_buffer.getvalue())
    return output.getvalue()


def build(repo: Path, commit: str, repository: str, workflow_url: str, output: Path) -> dict:
    if not re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repository):
        raise ValueError('Invalid repository identity')
    if not re.fullmatch(r'https://github\.com/' + re.escape(repository) + r'/actions/runs/[0-9]+', workflow_url):
        raise ValueError('Workflow URL must identify a run in the source repository')
    files = snapshot(repo, commit)
    manifest = validate_manifest(files)
    if not files[PDF_PATH][1].startswith(b'%PDF-'):
        raise ValueError('Expected manuscript PDF is absent or invalid')
    for name, path in EXTRA_ASSETS.items():
        if path not in files:
            raise ValueError('Required preprint/formalization asset missing: ' + path)
        if name.endswith('.pdf') and not files[path][1].startswith(b'%PDF-'):
            raise ValueError('Invalid preprint PDF')
    epoch = int(git(repo, 'show', '-s', '--format=%ct', commit).decode())
    tag = 'research-' + commit[:16]
    archive_name = tag + '.tar.gz'
    metadata = {
        'schema_version': 1,
        'repository': repository,
        'source_commit': commit,
        'source_tree': git(repo, 'show', '-s', '--format=%T', commit).decode().strip(),
        'source_commit_timestamp_untrusted': epoch,
        'timestamp_note': 'Commit dates are not trusted timestamps. Use the GitHub release publication time and verified Sigstore transparency-log record.',
        'workflow_url': workflow_url,
        'source_url': f'https://github.com/{repository}/tree/{commit}',
        'release_tag': tag,
        'source_archive': archive_name,
        'tracked_file_count': len(files),
        'manifest_pins': len(manifest['files']),
        'primary_documents': {PDF_ASSET: PDF_PATH, INTEGRATED_ASSET: INTEGRATED_PATH, **EXTRA_ASSETS},
        'release_manifest_sha256': sha256(files['RELEASE_MANIFEST.json'][1]),
        'scientific_status': 'Research manuscript with internal audits; provenance is not mathematical verification or an exclusive-priority certificate.',
        'formalization_status': 'Partial Lean formalization only; concrete Gaussian analytic components are checked, while the remaining geometric estimates and the full main theorem are not kernel-verified.',
    }
    payload = {
        archive_name: archive_bytes(files, tag, epoch),
        PDF_ASSET: files[PDF_PATH][1],
        INTEGRATED_ASSET: files[INTEGRATED_PATH][1],
        'RELEASE_MANIFEST.json': files['RELEASE_MANIFEST.json'][1],
        'SOURCE_METADATA.json': (json.dumps(metadata, indent=2, sort_keys=True) + '\n').encode(),
    }
    payload.update({name: files[path][1] for name, path in EXTRA_ASSETS.items()})
    payload['SHA256SUMS'] = ''.join(f'{sha256(content)}  {name}\n' for name, content in sorted(payload.items())).encode()
    if output.exists() and any(output.iterdir()):
        raise ValueError('Output directory must be empty')
    output.mkdir(parents=True, exist_ok=True)
    for name, content in payload.items():
        (output / name).write_bytes(content)
    return metadata


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path('.'))
    parser.add_argument('--commit', required=True)
    parser.add_argument('--repository', required=True)
    parser.add_argument('--workflow-url', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(build(args.repo, args.commit, args.repository, args.workflow_url, args.output), indent=2))


if __name__ == '__main__':
    main()
