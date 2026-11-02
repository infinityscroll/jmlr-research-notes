"""Integrity regressions for source snapshots and non-overwriting publication."""
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]

def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

builder = load('build_release')
publisher = load('publish_release')
preprint = load('build_preprint')


class SnapshotIntegrity(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / 'repo'
        self.repo.mkdir()
        self.git('init', '-q')
        self.git('config', 'user.name', 'Release fixture')
        self.git('config', 'user.email', 'fixture@example.invalid')
        self.write('proof.txt', b'The frozen proof.\n')
        self.write(builder.PDF_PATH, b'%PDF-1.4\nfixture\n')
        self.write(builder.INTEGRATED_PATH, b'Integrated theorem fixture.\n')
        for name, path in builder.EXTRA_ASSETS.items():
            self.write(path, b'%PDF-1.4\npreprint fixture\n' if name.endswith('.pdf') else b'Archive fixture\n')
        self.pin()
        self.commit = self.commit_all()

    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.repo), *args], stderr=subprocess.PIPE).decode().strip()

    def write(self, name, content):
        path = self.repo / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)

    def pin(self):
        files = {}
        for path in self.repo.rglob('*'):
            if path.is_file() and '.git' not in path.parts and path.name != 'RELEASE_MANIFEST.json':
                files[str(path.relative_to(self.repo))] = hashlib.sha256(path.read_bytes()).hexdigest()
        self.write('RELEASE_MANIFEST.json', (json.dumps({'files': files}) + '\n').encode())

    def commit_all(self):
        self.git('add', '.')
        self.git('commit', '-qm', 'Fixture snapshot')
        return self.git('rev-parse', 'HEAD')

    def build(self, directory, commit=None):
        return builder.build(self.repo, commit or self.commit, 'owner/repo',
                             'https://github.com/owner/repo/actions/runs/123', directory)

    def test_exact_commit_is_deterministic_and_excludes_local_changes(self):
        first, second = self.root / 'first', self.root / 'second'
        meta = self.build(first)
        self.write('proof.txt', b'Uncommitted replacement.\n')
        self.write('PRIVATE_TOKEN.txt', b'never publish this untracked fixture')
        self.build(second)
        for artifact in first.iterdir():
            self.assertEqual(artifact.read_bytes(), (second / artifact.name).read_bytes())
        with tarfile.open(fileobj=io.BytesIO((first / meta['source_archive']).read_bytes()), mode='r:gz') as archive:
            names = archive.getnames()
            self.assertFalse(any('PRIVATE_TOKEN' in name for name in names))
            self.assertEqual(archive.extractfile(meta['release_tag'] + '/proof.txt').read(), b'The frozen proof.\n')
        for line in (first / 'SHA256SUMS').read_text().splitlines():
            digest, name = line.split('  ', 1)
            self.assertEqual(digest, hashlib.sha256((first / name).read_bytes()).hexdigest())
        self.assertEqual(meta['source_commit'], self.commit)
        self.assertEqual(meta['manifest_pins'], 3 + len(builder.EXTRA_ASSETS))
        for name, path in builder.EXTRA_ASSETS.items():
            self.assertEqual((first / name).read_bytes(), (self.repo / path).read_bytes())
        self.assertIn('Partial Lean', meta['formalization_status'])
        self.assertIn('not trusted timestamps', meta['timestamp_note'])

    def test_committed_proof_change_without_new_pin_is_rejected(self):
        self.write('proof.txt', b'Changed proof but old pin.\n')
        changed = self.commit_all()
        with self.assertRaisesRegex(ValueError, 'Committed manifest mismatch'):
            self.build(self.root / 'bad', changed)

    def test_new_tracked_unpinned_file_is_rejected(self):
        self.write('unreviewed.txt', b'missing from manifest')
        changed = self.commit_all()
        with self.assertRaisesRegex(ValueError, 'every tracked file'):
            self.build(self.root / 'bad', changed)

    def test_symlinks_are_not_dereferenced_or_packaged(self):
        (self.repo / 'outside-link').symlink_to('/etc/passwd')
        changed = self.commit_all()
        with self.assertRaisesRegex(ValueError, 'Only regular tracked files'):
            self.build(self.root / 'bad', changed)

    def test_foreign_workflow_identity_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'source repository'):
            builder.build(self.repo, self.commit, 'owner/repo',
                          'https://github.com/attacker/repo/actions/runs/123', self.root / 'bad')


class PublicationIntegrity(unittest.TestCase):
    def test_draft_can_only_add_missing_assets_with_identical_existing_bytes(self):
        content = b'proof artifact'
        asset = {'name': 'proof.tar.gz', 'size': len(content),
                 'digest': 'sha256:' + hashlib.sha256(content).hexdigest()}
        self.assertEqual(publisher.asset_plan([asset], {'proof.tar.gz': content, 'metadata.json': b'{}'}), ['metadata.json'])
        with self.assertRaisesRegex(ValueError, 'differs'):
            publisher.asset_plan([asset], {'proof.tar.gz': b'a different proof'})
        with self.assertRaisesRegex(ValueError, 'Unexpected or duplicate'):
            publisher.asset_plan([asset, asset], {'proof.tar.gz': content})
        with self.assertRaisesRegex(ValueError, 'Unexpected or duplicate'):
            publisher.asset_plan([asset], {'another.tar.gz': content})

    def test_checksums_must_cover_every_primary_asset_once(self):
        payload = {'proof.tar.gz': b'proof', 'SOURCE_METADATA.json': b'{}',
                   'build-provenance.sigstore.json': b'bundle'}
        one = hashlib.sha256(payload['proof.tar.gz']).hexdigest() + '  proof.tar.gz\n'
        payload['SHA256SUMS'] = one.encode()
        with self.assertRaisesRegex(RuntimeError, 'entire primary payload'):
            publisher.validate_checksums(payload)
        payload['SHA256SUMS'] = (one + one).encode()
        with self.assertRaisesRegex(RuntimeError, 'duplicate'):
            publisher.validate_checksums(payload)
        two = hashlib.sha256(payload['SOURCE_METADATA.json']).hexdigest() + '  SOURCE_METADATA.json\n'
        payload['SHA256SUMS'] = (one + two).encode()
        publisher.validate_checksums(payload)

    def test_idempotent_published_release_cannot_skip_incomplete_assets(self):
        with mock.patch.object(publisher, 'tag_commit', return_value='a' * 40), \
             mock.patch.object(publisher, 'api', return_value=[]):
            with self.assertRaisesRegex(RuntimeError, 'complete asset set'):
                publisher.verify_published('owner/repo', 'research-tag', 'a' * 40,
                                           {'id': 1, 'draft': False, 'immutable': True})

    def test_explicitly_disabled_immutability_is_rejected(self):
        with mock.patch.object(publisher, 'api', return_value={'enabled': False}):
            with self.assertRaisesRegex(RuntimeError, 'must be enabled'):
                publisher.check_immutability('owner/repo')

    def test_published_release_requires_immutable_flag_and_matching_tag(self):
        release = {'draft': False, 'immutable': False}
        with self.assertRaisesRegex(RuntimeError, 'immutable'):
            publisher.verify_published('owner/repo', 'research-tag', 'a' * 40, release)
        with mock.patch.object(publisher, 'tag_commit', return_value='b' * 40):
            with self.assertRaisesRegex(RuntimeError, 'wrong source'):
                publisher.verify_published('owner/repo', 'research-tag', 'a' * 40, {'draft': False, 'immutable': True})


class FormalSourceBundleIntegrity(unittest.TestCase):
    def test_build_receipt_binds_sources_and_excludes_dependency_cache(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            directory = root / preprint.FORMAL
            directory.mkdir(parents=True)
            files = {'lean-toolchain': b'leanprover/lean4:v4.19.0\n',
                     'lake-manifest.json': b'{}\n',
                     'Proof.lean': b'theorem identity (P : Prop) (h : P) : P := h\n',
                     'third_party/dependency/LICENSE': b'Preserved upstream license\n',
                     'PORT.patch': b'Preserved compatibility diff\n'}
            for name, content in files.items():
                (directory / name).parent.mkdir(parents=True, exist_ok=True)
                (directory / name).write_bytes(content)
            receipt = {'status': 'passed', 'source_sha256':
                       {name: hashlib.sha256(data).hexdigest() for name, data in files.items()}}
            (directory / 'BUILD_RECEIPT.json').write_text(json.dumps(receipt))
            (directory / '.lake').mkdir()
            (directory / '.lake' / 'untracked.lean').write_text('Not a distributed proof')
            bundled = preprint.lean_files(root)
            self.assertEqual(set(bundled), set(files) | {'BUILD_RECEIPT.json'})
            (directory / 'Unrecorded.lean').write_text('Added after verification')
            with self.assertRaisesRegex(ValueError, 'cover every distributed file'):
                preprint.lean_files(root)
            (directory / 'Unrecorded.lean').unlink()
            (directory / 'Proof.lean').write_text('Changed source after the build')
            with self.assertRaisesRegex(ValueError, 'does not match distributed source'):
                preprint.lean_files(root)

    def test_source_archive_is_deterministic_and_rejects_unsafe_names(self):
        first = preprint.tar_bytes({'b.txt': b'B', 'a.txt': b'A'})
        self.assertEqual(first, preprint.tar_bytes({'a.txt': b'A', 'b.txt': b'B'}))
        with self.assertRaisesRegex(ValueError, 'Unsafe'):
            preprint.tar_bytes({'../outside.txt': b'X'})
        with tarfile.open(fileobj=io.BytesIO(first), mode='r:gz') as archive:
            self.assertEqual(archive.getnames(), ['a.txt', 'b.txt'])
            self.assertTrue(all(item.isfile() and item.mtime == 0 for item in archive))


if __name__ == '__main__':
    unittest.main()
