#!/usr/bin/env python3
"""Bundle the preprint, original proof companions, and partial Lean sources.

No third-party paper, Lean installation, mathlib checkout, or build cache is
redistributed. Archive times are normalized and make no priority assertion.
"""
from __future__ import annotations
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import tarfile

ROOT = Path(__file__).resolve().parents[1]
PROJECT = Path('preprints/negative-voting-simplex')
FORMAL = Path('formalization/negative-voting')
BASE = Path('frontier/negative-voting-simplex')
SOURCE_ARCHIVE = 'negative-voting-simplex-arxiv-source-2026-11-02.tar.gz'
LEAN_ARCHIVE = 'negative-voting-lean-2026-11-02.tar.gz'
COMPANIONS = {
    'original': BASE / 'dependency_review/proof_sources',
    'integrated': BASE / 'supplements/integrated-full-voting-proof-20261102',
    'classical-hodge': BASE / 'supplements/classical-hodge-normal-strain-20261102',
    'independent-hodge': BASE / 'supplements/independent-hodge-covariance-20261102',
    'independent-hazard': BASE / 'supplements/independent-hazard-certificate-20261102',
    'current-diagnostics': PROJECT / 'review',
}
PROOF_SUFFIXES = {'.txt', '.py'}
LEAN_SUFFIXES = {'.lean', '.toml', '.json', '.txt', '.py', '.sh', '.md'}
EXCLUDED_PARTS = {'.lake', '.git', '__pycache__', 'output', 'tmp'}


def digest(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def lean_files(root: Path) -> dict[str, bytes]:
    directory = root / FORMAL
    files = {}
    if not directory.is_dir():
        raise ValueError('Lean project is missing')
    for path in sorted(directory.rglob('*')):
        relative = path.relative_to(directory)
        if not path.is_file() or EXCLUDED_PARTS.intersection(relative.parts):
            continue
        if path.name == 'lean-toolchain' or path.suffix in LEAN_SUFFIXES:
            if path.is_symlink():
                raise ValueError('Symlinks are not distributable')
            files[relative.as_posix()] = path.read_bytes()
    if not {'lean-toolchain', 'lake-manifest.json'}.issubset(files):
        raise ValueError('Pinned Lean toolchain or dependency manifest is missing')
    if 'BUILD_RECEIPT.json' not in files:
        raise ValueError('A successful Lean build receipt is required')
    receipt = json.loads(files['BUILD_RECEIPT.json'])
    if receipt.get('status') != 'passed':
        raise ValueError('The recorded Lean build did not pass')
    for name, expected in receipt['source_sha256'].items():
        if name not in files or digest(files[name]) != expected:
            raise ValueError('Lean build receipt does not match distributed source: ' + name)
    return files


def companion_files(root: Path) -> tuple[dict[str, bytes], dict]:
    files, provenance = {}, {}
    for name, source in COMPANIONS.items():
        for path in sorted((root / source).rglob('*')):
            if not path.is_file() or (path.suffix not in PROOF_SUFFIXES and
                                     not (name == 'current-diagnostics' and path.suffix == '.json')):
                continue
            relative = path.relative_to(root / source)
            if EXCLUDED_PARTS.intersection(relative.parts):
                continue
            if path.is_symlink():
                raise ValueError('Symlinks are not distributable')
            target = 'anc/' + name + '/' + relative.as_posix()
            content = path.read_bytes()
            files[target] = content
            provenance[target] = {
                'repository_path': path.relative_to(root).as_posix(),
                'sha256': digest(content),
            }
    review = root / PROJECT / 'CRITICAL_DEPENDENCY_REVIEW.txt'
    if review.is_file():
        target = 'anc/current-diagnostics/CRITICAL_DEPENDENCY_REVIEW.txt'
        files[target] = review.read_bytes()
        provenance[target] = {'repository_path': review.relative_to(root).as_posix(),
                              'sha256': digest(files[target])}
    for name, content in lean_files(root).items():
        target = 'anc/lean/' + name
        files[target] = content
        provenance[target] = {
            'repository_path': (FORMAL / name).as_posix(),
            'sha256': digest(content),
        }
    manifest = {
        'description': 'Byte-identical original proof companions and partial Lean sources. Hashes establish identity, not correctness.',
        'formalization_scope': 'Partial formalization only. Gaussian analytic estimates and the full main theorem are not Lean-verified.',
        'files': provenance,
    }
    files['anc/SOURCE_MANIFEST.json'] = (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()
    return files, manifest


def tar_bytes(files: dict[str, bytes]) -> bytes:
    raw = io.BytesIO()
    with tarfile.open(fileobj=raw, mode='w', format=tarfile.PAX_FORMAT) as archive:
        for name, content in sorted(files.items()):
            if name.startswith('/') or '..' in Path(name).parts or not re.fullmatch(r'[A-Za-z0-9_+.,=/\-]+', name):
                raise ValueError('Unsafe or arXiv-incompatible archive name: ' + name)
            entry = tarfile.TarInfo(name)
            entry.size, entry.mtime, entry.mode = len(content), 0, 0o644
            entry.uid = entry.gid = 0
            entry.uname = entry.gname = ''
            archive.addfile(entry, io.BytesIO(content))
    target = io.BytesIO()
    with gzip.GzipFile(fileobj=target, mode='wb', filename='', mtime=0, compresslevel=9) as stream:
        stream.write(raw.getvalue())
    return target.getvalue()


def build(root: Path = ROOT, check: bool = False) -> dict:
    project = root / PROJECT
    files, manifest = companion_files(root)
    tex_files = sorted(project.glob('*.tex'))
    if not tex_files or not (project / 'main.tex').is_file():
        raise ValueError('Preprint LaTeX sources missing')
    for path in tex_files:
        files[path.name] = path.read_bytes()
    for path in sorted(project.glob('*.bib')) + sorted(project.glob('*.bbl')):
        files[path.name] = path.read_bytes()
    # Local inputs must be present; the bundle may not silently depend on the checkout.
    for path in tex_files:
        for command, target in re.findall(r'\\(input|include)\s*\{([^}]+)\}', path.read_text()):
            name = target if target.endswith('.tex') else target + '.tex'
            if name not in files:
                raise ValueError('Missing TeX input: ' + name)
    lean = lean_files(root)
    outputs = {
        root / 'archives' / SOURCE_ARCHIVE: tar_bytes(files),
        root / 'archives' / LEAN_ARCHIVE: tar_bytes({'negative-voting/' + name: content for name, content in lean.items()}),
    }
    for path, expected in outputs.items():
        if check:
            if not path.is_file() or path.read_bytes() != expected:
                raise ValueError('Stale or absent archive: ' + str(path.relative_to(root)))
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(expected)
    # The checked-in companion tree makes the manuscript usable without extraction.
    expected_anc = {name: content for name, content in files.items() if name.startswith('anc/')}
    if not check:
        anc = project / 'anc'
        if anc.exists():
            shutil.rmtree(anc)  # generated mirror only; originals live in frontier/ and formalization/
        for name, content in expected_anc.items():
            path = project / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)
    else:
        actual = {p.relative_to(project).as_posix(): p.read_bytes()
                  for p in (project / 'anc').rglob('*') if p.is_file()}
        if actual != expected_anc:
            raise ValueError('Ancillary mirror does not match the original sources')
    return {'arxiv_source_files': len(files), 'ancillary_source_pins': len(manifest['files']),
            'lean_source_files': len(lean),
            'archives': {p.name: digest(data) for p, data in outputs.items()}}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    print(json.dumps(build(check=args.check), indent=2))
