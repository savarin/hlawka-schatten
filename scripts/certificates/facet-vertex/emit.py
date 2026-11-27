#!/usr/bin/env python3
"""Emit the pinned facet and vertex sources into a new disposable directory."""

import argparse
from hashlib import file_digest, sha256
import json
from pathlib import Path
import runpy
import shutil
import subprocess
import sys
import tempfile
import zipfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import layout  # noqa: E402  (scripts/certificates/layout.py)


PACKAGE = Path(__file__).resolve().parent
R002 = 'lean-pilot/data/work__c1-tangent-cover__certs__cert_v2_rc0.002_eta0.002.txt.gz'


def digest(path):
    with path.open('rb') as data:
        return file_digest(data, 'sha256').hexdigest()


def check(path, expected):
    actual = digest(path)
    if actual != expected:
        raise ValueError(f'{path}: expected SHA-256 {expected}, got {actual}')


def read_manifest(path):
    result = {}
    for line in path.read_text().splitlines():
        expected, name = line.split('  ', 1)
        relative = Path(name)
        if relative.is_absolute() or '..' in relative.parts or relative in result:
            raise ValueError(f'Invalid manifest path {name}')
        result[relative] = expected
    return result


class Staging:
    def __init__(self, workspace, archive, source, inputs, expected):
        self.workspace = workspace
        self.archive = archive
        self.lean = workspace / 'lean'
        self.generators = workspace / 'generators'
        self.source = source
        self.expected = expected
        shutil.copytree(PACKAGE / 'generators', self.generators)
        for relative, pin in inputs.items():
            check(source / relative, pin)
            target = self.lean / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source / relative, target)
        for relative in expected:
            (self.lean / relative).parent.mkdir(parents=True, exist_ok=True)

    def run(self, script, *args):
        command = [sys.executable, '-I', '-S', '-B', self.generators / script, *args]
        subprocess.run(command, cwd=self.workspace, check=True)

    def load(self, script):
        return runpy.run_path(str(self.generators / script))


def fslab(stage, catalog):
    manifest = stage.workspace / 'fslab-data.jsonl'
    stage.run('f-slab-data.py', manifest, '--scheduled')
    check(manifest, catalog['fslab_manifest_sha256'])
    stage.run('f-slab-encode.py', manifest)
    stage.run('f-slab-join.py')


def facet_interior(stage, _catalog):
    manifest = stage.workspace / 'archived-facets.json'
    stage.run('facet-archive.py', stage.archive / 'glue/pilot', manifest)
    stage.run('facet-archive-real.py', manifest)
    stage.run('facet-archive-join.py', manifest)


def facet_g2(stage, _catalog):
    tip = stage.generators / 'g2-adaptive-tip.json'
    forest = stage.generators / 'g2-adaptive-upper-tree.jsonl'
    stage.run('g2-adaptive-encode.py', tip)
    encoder = stage.load('g2-adaptive-encode.py')
    table = encoder['Tables']()
    for line in forest.read_text().splitlines():
        row = json.loads(line)
        if row['kind'] == 'prism':
            encoder['encode'](row['leaf'], row, table, series='Upper')
    stage.run('g2-adaptive-real.py', tip)
    stage.run('g2-adaptive-real.py', forest, '--series', 'Upper')
    stage.run('g2-adaptive-assemble.py', forest, tip)


def e2(stage, _catalog):
    stage.run('e2-production-generate.py', stage.archive / R002, stage.archive / 'lean-pilot/Pilot')


def bulk_tables(stage, _catalog):
    pilot = stage.archive / 'lean-pilot/Pilot'
    for witness, predecessor, output in [
        ('Tab_fine', 'Checker', 'FineData'), ('R002_Tree', 'FineData', 'TreeData')
    ]:
        raw = (pilot / f'{witness}.lean').read_text()
        start = raw.index('namespace TC')
        stop = raw.index('set_option maxRecDepth', start)
        prelude = f'module\n\npublic import HlawkaSchatten.BelowExponent.Tangent.{predecessor}\n\n@[expose] public section\n\n'
        target = stage.lean / f'HlawkaSchatten/BelowExponent/Tangent/{output}.lean'
        target.write_text(prelude + raw[start:stop] + 'end TC\n')


def curvature_fallbacks(stage):
    emitter = stage.load('emit-vertex-curvature.py')
    vertex = stage.lean / 'HlawkaSchatten/BelowExponent/Vertex'
    prefix = Path('HlawkaSchatten/BelowExponent/Vertex/CurvatureData')
    roots = {cell: file.stem for file in (vertex / 'RootData').glob('*.lean')
             for cell in emitter['CELLS'].findall(file.read_text())}
    stems = {relative.relative_to(prefix).parts[0].removesuffix('.lean')
             for relative in stage.expected if relative.is_relative_to(prefix)}
    wanted = {name[0].lower() + name[1:] for name in stems}
    tables = ['vertex-curvature-candidates.tsv', 'vertex-curvature-vcm-refinements.tsv']
    for table in tables:
        for line in (stage.generators / table).read_text().splitlines():
            row = line.split('\t')
            if row[0] not in wanted:
                continue
            for name, content in emitter['emit'](row, roots):
                relative = prefix / f'{name}.lean'
                committed = layout.to_repo(relative.as_posix(), content, stage.source).encode()
                if sha256(committed).hexdigest() == stage.expected.get(relative):
                    (stage.lean / relative).write_text(content)


def vertex(stage, catalog):
    root_dir = stage.lean / 'HlawkaSchatten/BelowExponent/Vertex/RootData'
    index = stage.workspace / 'vertex-corner-index.json'
    stage.run('vertex_root_witnesses.py', stage.archive, root_dir)
    stage.run('vertex_corner_index.py', stage.archive, '--output', index)
    check(index, catalog['vertex_index_sha256'])
    stage.run('emit-vc-corner-links.py', index)
    stage.run('emit-vertex-curvature-cut.py', index)
    curvature_fallbacks(stage)
    stage.run('corner-power-generate.py')
    stage.run('vc-cut-points.py')
    stage.run('sc-outer-generate.py', '--cut')
    stage.run('sc-outer-generate.py', '--cut', '--wide-witnesses')
    stage.load('sc-near-coarse-batches.py')['assemble_sources']()


ACTIONS = {'fslab': fslab, 'facet-interior': facet_interior, 'facet-g2': facet_g2,
           'e2': e2, 'bulk-tables': bulk_tables, 'vertex': vertex}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('family', choices=ACTIONS)
    parser.add_argument('--lean-source', type=Path, default=PACKAGE.parents[2],
                        help='source checkout supplying the input Lean literals')
    parser.add_argument('--archive-root', type=Path, help='use an existing copy of the retained witnesses')
    parser.add_argument('--output', type=Path, required=True, help='new directory for the verified Lean files')
    args = parser.parse_args()

    catalog = json.loads((PACKAGE / 'catalog.json').read_text())
    spec = catalog['families'][args.family]
    for relative, pin in catalog['bundled_inputs'].items():
        check(PACKAGE / relative, pin)
    manifest = PACKAGE / spec['outputs']
    check(manifest, spec['output_manifest_sha256'])
    expected = read_manifest(manifest)
    if len(expected) != spec['files']:
        raise ValueError('The output manifest count differs from the catalog')
    out = args.output.resolve()
    if out.exists():
        parser.error(f'Choose a new output directory: {out} already exists')
    out.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.hlawka-emit-', dir=out.parent) as temporary:
        work = Path(temporary)
        archive = args.archive_root
        if spec['external_inputs'] and archive is None:
            archive = work / 'retained'
            bundle = PACKAGE / 'witnesses.zip'
            check(bundle, catalog['witness_archive_sha256'])
            with zipfile.ZipFile(bundle) as witnesses:
                for name in spec['external_inputs']:
                    relative = Path(name)
                    if relative.is_absolute() or '..' in relative.parts:
                        raise ValueError(f'Invalid witness path {name}')
                    target = archive / relative
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(witnesses.read(name))
        for name, pin in spec['external_inputs'].items():
            check(archive / name, pin)
        stage = Staging(work, archive, args.lean_source, spec['source_inputs'], expected)
        ACTIONS[args.family](stage, catalog)
        ready = stage.workspace / 'verified'
        for relative, pin in expected.items():
            target = ready / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            text = (stage.lean / relative).read_text(encoding='utf-8')
            target.write_text(layout.to_repo(relative.as_posix(), text, stage.source), encoding='utf-8')
            check(target, pin)
        ready.rename(out)
    print(f'Matched {len(expected)} Lean files in {out}')


if __name__ == '__main__':
    main()
