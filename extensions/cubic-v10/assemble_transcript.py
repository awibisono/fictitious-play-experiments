"""Reconstruct and hash-check the exact archived gzip transcript from its parts."""
from pathlib import Path
import hashlib, json
R = Path(__file__).resolve().parent
manifest = json.loads((R / 'transcript_parts.json').read_text())
out = R / manifest['filename']
def sha(data):
    return hashlib.sha256(data).hexdigest()
if out.exists():
    if sha(out.read_bytes()) != manifest['sha256']:
        raise RuntimeError('Existing transcript differs; move it aside before reconstructing')
    print('Existing transcript hash verified:', out.name)
else:
    chunks = []
    for part in manifest['parts']:
        data = (R / part['name']).read_bytes()
        if len(data) != part['size'] or sha(data) != part['sha256']:
            raise RuntimeError('Transcript part failed validation: ' + part['name'])
        chunks.append(data)
    data = b''.join(chunks)
    if len(data) != manifest['size'] or sha(data) != manifest['sha256']:
        raise RuntimeError('Reconstructed transcript failed validation')
    with out.open('xb') as f:
        f.write(data)
    print('Reconstructed transcript hash verified:', out.name)
