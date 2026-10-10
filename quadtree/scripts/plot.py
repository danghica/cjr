#!/usr/bin/env python3
"""Draw self-contained benchmark SVGs using only the Python standard library."""
import html
import json
import math
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]
DATA = json.loads((ROOT / 'benchmark/results/summary.json').read_text())
WORKLOADS = ['build', 'hits', 'misses', 'empty', 'selective', 'broad', 'whole']
IMPLEMENTATIONS = [('CJR', '#176f76'), ('Native', '#de8b37'), ('Flat', '#8562a0')]
SIZES = [256, 4096, 16384]
WIDTH, HEIGHT = 1120, 680


def esc(value):
    return html.escape(str(value), quote=True)


def chart(distribution):
    panels = []
    for index, workload in enumerate(WORKLOADS):
        col, row = index % 4, index // 4
        x0, y0 = 22 + col * 274, 62 + row * 292
        left, top, width, height = x0 + 45, y0 + 36, 208, 200
        values = [r for r in DATA if r['distribution'] == distribution and r['workload'] == workload]
        low = min(r['q1_ns'] for r in values)
        high = max(r['q3_ns'] for r in values)
        lo, hi = math.floor(math.log10(low)), math.ceil(math.log10(high))
        if lo == hi:
            lo -= 1
            hi += 1
        def py(value):
            return top + height * (hi - math.log10(value)) / (hi - lo)
        parts = [f'<text x="{left}" y="{y0+20}" class="title">{esc(workload)}</text>']
        for decade in range(lo, hi + 1):
            y = py(10 ** decade)
            parts.append(f'<path d="M {left} {y:.1f} H {left+width}" class="grid"/><text x="{left-7}" y="{y+4:.1f}" text-anchor="end" class="tick">10^{decade}</text>')
        for j, size in enumerate(SIZES):
            x = left + j * width / 2
            parts.append(f'<text x="{x:.1f}" y="{top+height+20}" text-anchor="middle" class="tick">{size:,}</text>')
        parts.append(f'<path d="M {left} {top} V {top+height} H {left+width}" class="axis"/>')
        for name, color in IMPLEMENTATIONS:
            points = []
            for j, size in enumerate(SIZES):
                item = next(r for r in values if r['implementation'] == name and r['n'] == size)
                x = left + j * width / 2
                median, q1, q3 = item['median_ns'], item['q1_ns'], item['q3_ns']
                y, y1, y3 = py(median), py(q1), py(q3)
                points.append(f'{x:.1f},{y:.1f}')
                parts.append(f'<path d="M {x:.1f} {y3:.1f} V {y1:.1f} M {x-4:.1f} {y3:.1f} H {x+4:.1f} M {x-4:.1f} {y1:.1f} H {x+4:.1f}" stroke="{color}" stroke-width="1.5"/>')
                parts.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="3.5" fill="{color}"/>')
            parts.append(f'<polyline points="{" ".join(points)}" fill="none" stroke="{color}" stroke-width="2"/>')
        unit = 'µs / point' if workload in ['build', 'hits', 'misses'] else 'µs / query'
        parts.append(f'<text x="{left+width/2}" y="{top+height+43}" text-anchor="middle" class="tick">points (log scale)</text><text x="{x0+9}" y="{top+height/2}" text-anchor="middle" class="tick" transform="rotate(-90 {x0+9} {top+height/2})">{unit} (log)</text>')
        panels.extend(parts)
    legend = ''.join(f'<g transform="translate({360+i*140},34)"><path d="M 0 0 H 26" stroke="{color}" stroke-width="3"/><text x="33" y="4" class="tick">{name}</text></g>' for i, (name, color) in enumerate(IMPLEMENTATIONS))
    return f'''<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {WIDTH} {HEIGHT}" role="img" aria-labelledby="title description">
<title id="title">Quadtree benchmark — {esc(distribution)} points</title>
<desc id="description">Median timings and interquartile ranges across 21 trials, split into seven workloads and three implementations.</desc>
<style>text{{font-family:system-ui,-apple-system,sans-serif;fill:#26333a}}.headline{{font-size:20px;font-weight:650}}.title{{font-size:13px;font-weight:600}}.tick{{font-size:10px}}.grid{{stroke:#dfe6e8;stroke-width:1}}.axis{{fill:none;stroke:#718087;stroke-width:1.2}}</style>
<rect width="100%" height="100%" fill="#fff"/><text x="24" y="30" class="headline">{esc(distribution.title())} distribution · median and IQR · 21 trials</text>{legend}{''.join(panels)}</svg>'''


for distribution in ['uniform', 'cluster', 'prefix']:
    (ROOT / f'benchmark/results/{distribution}.svg').write_text(chart(distribution))
