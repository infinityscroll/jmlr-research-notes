#!/usr/bin/env python3
"""Publish complete drafts without replacing tags or existing asset bytes."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request

API = 'https://api.github.com'


def api(method, path, data=None, missing_ok=False):
    body = None if data is None else json.dumps(data).encode()
    request = urllib.request.Request(API + path, data=body, method=method, headers={
        'Authorization': 'Bearer ' + os.environ['GH_TOKEN'],
        'Accept': 'application/vnd.github+json',
        'X-GitHub-Api-Version': '2026-03-10',
        'Content-Type': 'application/json',
    })
    try:
        with urllib.request.urlopen(request) as response:
            raw = response.read()
            return json.loads(raw) if raw else None
    except urllib.error.HTTPError as error:
        if error.code == 404 and missing_ok:
            return None
        raise RuntimeError(f'GitHub API {method} {path}: HTTP {error.code}') from error


def check_immutability(repository):
    try:
        setting = api('GET', f'/repos/{repository}/immutable-releases')
    except RuntimeError as error:
        if 'HTTP 403' in str(error) or 'HTTP 404' in str(error):
            print('::warning::Repository setting requires admin-read permission; published release immutability will be verified before success.')
            return
        raise
    if setting.get('enabled') is not True:
        raise RuntimeError('Immutable releases must be enabled in repository settings')


def tag_commit(repository, tag):
    ref = api('GET', f'/repos/{repository}/git/ref/tags/{tag}', missing_ok=True)
    if ref is None:
        return None
    obj = ref['object']
    for _ in range(8):
        if obj['type'] == 'commit':
            return obj['sha']
        if obj['type'] != 'tag':
            break
        obj = api('GET', f'/repos/{repository}/git/tags/{obj["sha"]}')['object']
    raise RuntimeError('Tag does not resolve directly to an expected commit')


def download_asset(repository, asset, destination):
    with destination.open('wb') as stream:
        subprocess.run(['gh', 'api', f'repos/{repository}/releases/assets/{int(asset["id"])}',
                        '-H', 'Accept: application/octet-stream'], stdout=stream, check=True)
    data = destination.read_bytes()
    if asset.get('digest') != 'sha256:' + hashlib.sha256(data).hexdigest() or len(data) != asset['size']:
        raise RuntimeError('Downloaded release asset digest does not match GitHub')


def verify_provenance(repository, commit, directory, names):
    for name in sorted(names):
        subprocess.run(['gh', 'attestation', 'verify', str(directory / name), '--repo', repository,
                        '--bundle', str(directory / 'build-provenance.sigstore.json'),
                        '--signer-workflow', repository + '/.github/workflows/release.yml',
                        '--signer-digest', commit, '--source-digest', commit,
                        '--source-ref', 'refs/heads/main'], check=True)


def expected_names(tag):
    return {tag + '.tar.gz', 'negative_gaussian_simplex_stability_v2.pdf',
            'negative_voting_integrated_proof_20261102.txt',
            'RELEASE_MANIFEST.json', 'SOURCE_METADATA.json', 'SHA256SUMS',
            'build-provenance.sigstore.json'}


def validate_checksums(payload):
    required = set(payload) - {'SHA256SUMS', 'build-provenance.sigstore.json'}
    seen = set()
    for line in payload['SHA256SUMS'].decode().splitlines():
        digest, name = line.split('  ', 1)
        if name in seen or name not in required or not re.fullmatch(r'[0-9a-f]{64}', digest):
            raise RuntimeError('Unexpected or duplicate checksum entry')
        seen.add(name)
        if hashlib.sha256(payload[name]).hexdigest() != digest:
            raise RuntimeError('Release checksum validation failed')
    if seen != required:
        raise RuntimeError('Checksum file does not cover the entire primary payload')


def verify_published(repository, tag, commit, release):
    if release.get('draft') or release.get('immutable') is not True:
        raise RuntimeError('Release is not published and immutable')
    if tag_commit(repository, tag) != commit:
        raise RuntimeError('Published tag has the wrong source commit')
    assets = api('GET', f'/repos/{repository}/releases/{release["id"]}/assets?per_page=100')
    names = [asset['name'] for asset in assets]
    if len(names) != len(set(names)) or set(names) != expected_names(tag):
        raise RuntimeError('Published release does not contain the expected complete asset set')
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp)
        for asset in assets:
            download_asset(repository, asset, directory / asset['name'])
        payload = {name: (directory / name).read_bytes() for name in names}
        validate_checksums(payload)
        metadata = json.loads(payload['SOURCE_METADATA.json'])
        if (metadata['source_commit'] != commit or metadata['repository'] != repository
                or metadata['release_tag'] != tag or metadata['source_archive'] != tag + '.tar.gz'):
            raise RuntimeError('Published metadata has the wrong source identity')
        verify_provenance(repository, commit, directory, set(names) - {'build-provenance.sigstore.json'})
    for attempt in range(3):
        result = subprocess.run(['gh', 'release', 'verify', tag, '--repo', repository])
        if result.returncode == 0:
            break
        if attempt == 2:
            raise RuntimeError('Immutable release attestation verification failed')
        time.sleep(2)


def asset_plan(existing, payload):
    """Reject a partial release conflict; never delete or replace asset bytes."""
    by_name = {}
    for asset in existing:
        name = asset['name']
        if name in by_name or name not in payload:
            raise ValueError(f'Unexpected or duplicate release asset: {name}')
        by_name[name] = asset
        expected = 'sha256:' + hashlib.sha256(payload[name]).hexdigest()
        if asset.get('digest') != expected or asset.get('size') != len(payload[name]):
            raise ValueError(f'Existing release asset differs: {name}')
    return [name for name in sorted(payload) if name not in by_name]


def output(name, value):
    if '\n' in str(value) or '\r' in str(value):
        raise ValueError('Unsafe workflow output')
    if os.environ.get('GITHUB_OUTPUT'):
        with open(os.environ['GITHUB_OUTPUT'], 'a', encoding='utf-8') as stream:
            stream.write(f'{name}={value}\n')
    print(f'{name}={value}')


def prepare(repository, commit):
    tag = 'research-' + commit[:16]
    check_immutability(repository)
    resolved = tag_commit(repository, tag)
    if resolved not in (None, commit):
        raise RuntimeError('Existing tag points elsewhere; refusing to move it')
    release = api('GET', f'/repos/{repository}/releases/tags/{tag}', missing_ok=True)
    if release and not release['draft']:
        verify_published(repository, tag, commit, release)
        output('skip', 'true')
        output('release_url', release['html_url'])
    else:
        output('skip', 'false')
    output('tag', tag)


def publish(repository, commit, directory):
    tag = 'research-' + commit[:16]
    check_immutability(repository)
    meta = json.loads((directory / 'SOURCE_METADATA.json').read_text())
    if meta['source_commit'] != commit or meta['repository'] != repository or meta['release_tag'] != tag:
        raise RuntimeError('Artifact metadata does not match release identity')
    if meta['source_archive'] != tag + '.tar.gz':
        raise RuntimeError('Unexpected source archive identity')
    resolved = tag_commit(repository, tag)
    if resolved not in (None, commit):
        raise RuntimeError('Refusing to publish over a different tag commit')
    release = api('GET', f'/repos/{repository}/releases/tags/{tag}', missing_ok=True)
    if release and not release['draft']:
        verify_published(repository, tag, commit, release)
        output('release_url', release['html_url'])
        return
    if release:
        if release.get('target_commitish') != commit or release['tag_name'] != tag:
            raise RuntimeError('Existing draft identity differs; refusing to modify it')
        # A rerun can reuse a previously uploaded signed bundle. It is verified
        # against every freshly built primary asset below; nothing is overwritten remotely.
        existing = api('GET', f'/repos/{repository}/releases/{release["id"]}/assets?per_page=100')
        bundles = [asset for asset in existing if asset['name'] == 'build-provenance.sigstore.json']
        if len(bundles) > 1:
            raise RuntimeError('Duplicate provenance bundle in draft')
        if bundles:
            download_asset(repository, bundles[0], directory / 'build-provenance.sigstore.json')
    payload = {p.name: p.read_bytes() for p in directory.iterdir() if p.is_file()}
    required = expected_names(tag)
    if set(payload) != required:
        raise RuntimeError('Release payload is incomplete or contains unexpected files')
    validate_checksums(payload)
    # The bundle is cryptographically signed rather than self-listed in SHA256SUMS.
    verify_provenance(repository, commit, directory, required - {'build-provenance.sigstore.json'})
    if release is None:
        body = (f'Exact source commit: `{commit}`\n\n'
                f'Source snapshot and checksums were built by {meta["workflow_url"]}. '
                'All release assets are uploaded before publication. GitHub release immutability '
                'locks the published tag and assets. Build provenance uses GitHub Actions OIDC '
                'and Sigstore attestations.\n\n'
                'The archive contains the complete tracked source tree, including the current '
                'proof notes and reviews. The standalone PDF is the preserved v2 manuscript; '
                'the latest integrated theorem is also attached as a standalone text asset, '
                'and its supporting supplements are in the source archive.\n\n'
                'Use the server-recorded publication time and verified transparency-log record '
                'as evidence of existence. Commit dates are not trusted timestamps. '
                'This records provenance; it does not certify mathematical correctness or '
                'exclusive scientific priority. See RELEASING.txt for verification commands.')
        release = api('POST', f'/repos/{repository}/releases', {
            'tag_name': tag, 'target_commitish': commit, 'name': 'Research snapshot ' + commit[:16],
            'body': body, 'draft': True, 'prerelease': True, 'make_latest': 'false',
        })
    if release.get('target_commitish') != commit or release['tag_name'] != tag:
        raise RuntimeError('Existing draft identity differs; refusing to modify it')
    assets = api('GET', f'/repos/{repository}/releases/{release["id"]}/assets?per_page=100')
    for name in asset_plan(assets, payload):
        # gh performs authenticated upload without exposing the token or clobbering assets.
        subprocess.run(['gh', 'release', 'upload', tag, str(directory / name), '--repo', repository], check=True)
    assets = api('GET', f'/repos/{repository}/releases/{release["id"]}/assets?per_page=100')
    if asset_plan(assets, payload):
        raise RuntimeError('Not all expected assets are present')
    release = api('PATCH', f'/repos/{repository}/releases/{release["id"]}', {'draft': False, 'make_latest': 'false'})
    verify_published(repository, tag, commit, release)
    output('release_url', release['html_url'])
    if os.environ.get('GITHUB_STEP_SUMMARY'):
        with open(os.environ['GITHUB_STEP_SUMMARY'], 'a', encoding='utf-8') as stream:
            stream.write(f'Immutable release: [{tag}]({release["html_url"]})\n\nSource commit: `{commit}`\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('prepare', 'publish'))
    parser.add_argument('--repository', required=True)
    parser.add_argument('--commit', required=True)
    parser.add_argument('--directory', type=Path)
    args = parser.parse_args()
    if not re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', args.repository):
        raise ValueError('Invalid repository')
    if not re.fullmatch(r'[0-9a-f]{40}|[0-9a-f]{64}', args.commit):
        raise ValueError('A full commit ID is required')
    if args.command == 'prepare':
        prepare(args.repository, args.commit)
    else:
        if args.directory is None:
            parser.error('--directory is required for publish')
        publish(args.repository, args.commit, args.directory)


if __name__ == '__main__':
    main()
