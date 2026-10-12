"""Check the content-addressed, commit-pinned research snapshot locally."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root/'provenance/source-manifest.json').read_text())
for record in manifest['files']:
    data = (root/record['local_path']).read_bytes()
    blob = b'blob '+str(len(data)).encode()+b'\0'+data
    assert hashlib.sha1(blob).hexdigest() == record['git_blob_sha1'], record['local_path']
    assert hashlib.sha256(data).hexdigest() == record['sha256'], record['local_path']
for record in manifest['auxiliary_files']:
    assert hashlib.sha256((root/record['local_path']).read_bytes()).hexdigest() == record['sha256']
print('Passed: 29 source Git blobs and all auxiliary fingerprints')
