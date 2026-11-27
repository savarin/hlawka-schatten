"""Generate the exact inputs for the native curvature candidate search."""

import argparse
from fractions import Fraction
import json
from math import prod
from pathlib import Path
import runpy

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('corner_index', type=Path)
parser.add_argument('output', type=Path)
arguments = parser.parse_args()

HERE = Path(__file__).resolve().parent
GENERATORS = HERE.parent / 'generators'
root_intervals = runpy.run_path(str(GENERATORS / 'vertex_root_witnesses.py'))['root_intervals']
index = json.loads(arguments.corner_index.read_text())
old = {}
for filename in ('vertex-curvature-candidates.tsv', 'vertex-curvature-vcm-refinements.tsv'):
    for line in (GENERATORS / filename).read_text().splitlines():
        cols = line.split('\t')
        old[cols[0]] = (prod(map(int, cols[1:4])), tuple(map(Fraction, cols[-3:])))

source = ['import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.PointTable', 'import HlawkaSchatten.BelowExponent.Vertex.SideCornerData.RootTable',
          'import HlawkaSchatten.BelowExponent.Vertex.SideOuterTreeSearch', 'import HlawkaSchatten.BelowExponent.Vertex.SideOuterWideCheck',
          'import HlawkaSchatten.BelowExponent.Vertex.SideOuterCheck', '', 'set_option maxRecDepth 30000', '',
          'open HlawkaSchatten.BelowExponent.Vertex', '', 'structure CurvatureCutInput where', '  name : String',
          '  cell : ParameterCell', '  roots : Fin 3 → RatBounds', '  oldVolume : Nat',
          '  oldMargins : Vector ℚ 3', '  corners : Vector Nat 8', '']


def array_groups(name, type_, records):
    groups = []
    for start in range(0, len(records), 32):
        group = f'{name}{start:03}'
        groups.append(group)
        source.extend((f'private def {group} : Array ({type_}) := #[',
                       '  ' + ',\n  '.join(records[start:start+32]) + ']', ''))
    source.extend((f'private def {name} : Array ({type_}) :=', '  ' + ' ++\n  '.join(groups), ''))


def pair(lo, hi):
    return f'⟨{lo}, {hi}⟩'


for family in ('VC','SC'):
    data = index[family]
    points = [tuple(map(Fraction, p)) for p in data['points']]
    records = []
    for cell in data['cells']:
        label = cell['zone'][0].lower() + cell['zone'][1:] + str(cell['parent'])
        if label not in old:
            label += f"Child{cell['child']}"
        volume, old_margin = old[label]
        corner_ids = cell['corners']
        spans = list(zip(points[corner_ids[0]], points[corner_ids[-1]], strict=True))
        roots = root_intervals(spans)
        corners = ', '.join(map(str, corner_ids))
        old_str = ', '.join(map(str, old_margin))
        box_str = ', '.join(pair(lo,hi) for lo,hi in spans)
        roots_str = ', '.join(pair(lo,hi) for lo,hi in roots)
        records.append(f'⟨{json.dumps(label)}, ⟨{box_str}⟩, ![{roots_str}], {volume}, #v[{old_str}], #v[{corners}]⟩')
    array_groups(f'{family.lower()}CutCells', 'CurvatureCutInput', records)
array_groups('vcCutRoots', 'Fin 3 → RatBounds', [f'vcOuterP{i:03}Roots' for i in range(882)])
source.append((HERE / 'vertex-curvature-cut-search.lean').read_text())
arguments.output.write_text('\n'.join(source))
