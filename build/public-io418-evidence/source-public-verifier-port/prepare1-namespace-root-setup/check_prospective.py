"""Assigned 13d9 three-module gate; never writes to the authoritative lender."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path('/home/cody/zisk-fv-source-public-verifier-port')
HERE = Path(__file__).resolve().parent
LEASE = Path('/home/cody/zisk-fv-api-loads-approved/build/native-shared-proper448-evidence/readonly-source-public-verifier-lease.json')
LEASE_SHA = '85a9b2e0fd5941a87088947d7e0ee6d1c20fdbcdf73310b740b24a5512632a54'
MODULES = [
    ('ZiskFv/AirsClean/PublicIo', 'b4e033df8a4870ca3ec3017cf9c5117aa5bb8f7c6c0e45bcfe915ea1dac9ad46'),
    ('ZiskFv/AirsClean/PublicIoSource', '200083485eb12bcc1e8da4610d37e08ffd5e0130ca182a6e350c92cd20c6e5f7'),
    ('ZiskFv/AirsClean/SourcePublicVerifier', '8cf02c690a721cf44a4026a2c61fc925d22051555c9266a6b8ee9c46ea186afa'),
]
OUT = HERE / 'prospective-gate/out'
OVERLAY = HERE / 'prospective-gate/readonly'
OPTIONS = ['-j2', '--tstack=400000', '-Dpp.unicode.fun=true']


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def save(path, data):
    Path(path).write_text(json.dumps(data, indent=2) + '\n')


def verify(lease, phase):
    started = time.monotonic()
    assert sha(LEASE) == LEASE_SHA, 'Authoritative lease file changed'
    assert lease['source_head'] == '622938be281db14470819a9fe752528221a2491d'
    assert lease['options'] == OPTIONS
    assert sha(lease['compiler']) == lease['compiler_sha256'], 'Compiler changed'
    for module, expected in MODULES:
        assert sha(ROOT / (module + '.lean')) == expected, module + ' source changed'
    lender = Path(lease['lender'])
    for relative, expected in lease['source_sha256'].items():
        assert sha(lender / relative) == expected, 'Lender source changed: ' + relative
        # Only the explicitly approved three ordinary aggregate exports differ.
        if relative != 'ZiskFv.lean':
            assert sha(ROOT / relative) == expected, 'Local prerequisite differs: ' + relative
    for name, record in lease['generated34'].items():
        assert sha(record['path']) == record['sha256'], 'Generated source changed: ' + name
    for path, record in lease['cache_objects_and_ir_sidecars'].items():
        actual = Path(path)
        assert actual.stat().st_size == record['bytes'], 'Borrowed object size changed: ' + path
        assert sha(actual) == record['sha256'], 'Borrowed object/IR changed: ' + path
    result = {
        'phase': phase, 'status': 'ALL_EXACT',
        'lease_sha256': LEASE_SHA, 'tracked_sources': len(lease['source_sha256']),
        'generated_sources': len(lease['generated34']),
        'objects_including_ir': len(lease['cache_objects_and_ir_sidecars']),
        'seconds': time.monotonic() - started,
    }
    save(HERE / (phase + '-strict-lease.json'), result)
    print(json.dumps(result), flush=True)
    return result


def make_environment(lease):
    assert not OUT.exists() and not OVERLAY.exists(), 'Fresh owned gate destinations already exist'
    OUT.mkdir(parents=True)
    overlay_paths = []
    linked = 0
    excluded = []
    originals = [Path(p) for p in lease['lean_path_absolute'].split(os.pathsep)]
    for index, original in enumerate(originals):
        target = OVERLAY / str(index)
        target.mkdir(parents=True)
        overlay_paths.append(target)
        for path in lease['cache_objects_and_ir_sidecars']:
            source = Path(path)
            if not source.is_relative_to(original):
                continue
            relative = source.relative_to(original)
            if any(relative.as_posix().startswith(module + '.') for module, _ in MODULES):
                excluded.append(path)
                continue
            link = target / relative
            link.parent.mkdir(parents=True, exist_ok=True)
            link.symlink_to(source)
            linked += 1
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(map(str, [OUT, *overlay_paths]))
    env['LEAN_NUM_THREADS'] = '2'
    env['CARGO_BUILD_JOBS'] = '2'
    save(HERE / 'prospective-environment.json', {
        'compiler': lease['compiler'], 'compiler_sha256': lease['compiler_sha256'],
        'options': OPTIONS, 'LEAN_PATH': env['LEAN_PATH'],
        'source_head': lease['source_head'], 'readonly_metadata_symlinks': linked,
        'excluded_new_modules_and_all_sidecars': excluded,
        'fresh_prerequisites': [], 'object_or_cache_copies': 0,
        'foreign_writes': 0,
    })
    return env


def run(lease, env, label, source, output=None):
    command = [lease['compiler'], *OPTIONS, '--root=' + str(ROOT)]
    if output is not None:
        output.parent.mkdir(parents=True, exist_ok=True)
        command += ['-o', str(output.with_suffix('.olean')), '-i', str(output.with_suffix('.ilean'))]
    command.append(str(source))
    save(HERE / (label + '.command.json'), {
        'argv': command, 'cwd': str(ROOT), 'LEAN_PATH': env['LEAN_PATH'],
        'compiler_sha256': lease['compiler_sha256'], 'source_sha256': sha(source),
    })
    started = time.monotonic()
    with (HERE / (label + '.log')).open('w') as log:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
    record = {'label': label, 'status': result.returncode, 'seconds': time.monotonic() - started}
    save(HERE / (label + '.result.json'), record)
    print(json.dumps(record), flush=True)
    assert result.returncode == 0, label + ' failed; actual diagnostics preserved'
    return record


def main():
    assert sha(LEASE) == LEASE_SHA, 'Wrong authoritative lease'
    lease = json.loads(LEASE.read_text())
    assert lease['proper_standard_prefix_status'] == 0
    assert lease['options'] == OPTIONS
    sources = {str(ROOT / (module + '.lean')): sha(ROOT / (module + '.lean')) for module, _ in MODULES}
    for path in [ROOT / 'ZiskFv.lean', ROOT / 'README.md', Path(__file__), HERE / 'MeasureStandalonePublicModelsRaw.lean']:
        sources[str(path)] = sha(path)
    save(HERE / 'prospective-source-freeze.json', {
        'source_commit': '13d9d01296961e984f73645fd23942547aede8e7',
        'base': lease['source_head'], 'authoritative_lease': str(LEASE),
        'authoritative_lease_sha256': LEASE_SHA, 'source_sha256': sources,
        'scope': 'NEW three defining modules, not previous leaf76; no canonical world retarget',
    })
    verify(lease, 'before')
    results = []
    try:
        env = make_environment(lease)
        for module, _ in MODULES:
            results.append(run(lease, env, 'narrow-' + module.replace('/', '_'), ROOT / (module + '.lean'), OUT / module))
        results.append(run(lease, env, 'full-all-three', HERE / 'MeasureStandalonePublicModelsRaw.lean'))
        report = json.loads((HERE / 'full-raw-axioms.json').read_text())
        standard = ['Classical.choice', 'Quot.sound', 'propext']
        assert sorted(report['raw_axioms']) == standard, 'Observed nonstandard RAW axioms; report retained unfiltered'
        assert report['independent_per_root_and_union_match'] is True
        assert len(report['per_root']) == len(report['declarations'])
        save(HERE / 'prospective-result.json', {
            'status': 'GREEN', 'base': lease['source_head'], 'checks': results,
            'all_three_defining_modules': report['modules'],
            'declarations': len(report['declarations']), 'raw_axioms': report['raw_axioms'],
            'opaque_types_values_private_compiler_constructors_full_paths': True,
            'every_root_and_union_independent_collectAxioms': True,
            'no_new_authentication_accepted_Sail_or_354_418_closure_claim': True,
        })
        own_objects = {str(path): {'sha256': sha(path), 'bytes': path.stat().st_size} for path in OUT.rglob('*') if path.is_file()}
        save(HERE / 'checked-prospective-three-lease.json', {
            'source_commit': '13d9d01296961e984f73645fd23942547aede8e7',
            'base': lease['source_head'], 'source_sha256': sources,
            'borrowed_authoritative_lease': str(LEASE), 'borrowed_lease_sha256': LEASE_SHA,
            'compiler': lease['compiler'], 'compiler_sha256': lease['compiler_sha256'],
            'options': OPTIONS, 'LEAN_PATH': env['LEAN_PATH'], 'fresh_owned_objects': own_objects,
            'defining_modules': report['modules'], 'roots': len(report['declarations']),
            'raw_axioms': report['raw_axioms'],
        })
    finally:
        verify(lease, 'after')
        for path, expected in sources.items():
            assert sha(path) == expected, 'Frozen owned source/observer changed: ' + path


if __name__ == '__main__':
    main()
