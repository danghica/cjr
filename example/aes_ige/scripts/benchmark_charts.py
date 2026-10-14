#!/usr/bin/env python3
"""Log-scale median/IQR plots for the native-versus-extracted comparison."""
import html
import json
import math
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main():
    output=ROOT/'benchmark/results'
    data=json.loads((output/'summary.json').read_text())
    for case in sorted({r['case'] for r in data}):
        rows=[r for r in data if r['case']==case]
        groups=sorted({r['n'] for r in rows})
        lo=math.floor(math.log10(min(r['q1_ns'] for r in rows)))
        hi=math.ceil(math.log10(max(r['q3_ns'] for r in rows)))
        if lo==hi: hi+=1
        x=lambda v: 180+620*(math.log10(v)-lo)/(hi-lo)
        height=110+len(groups)*90
        unit='ns/expansion' if case.startswith('key_') else 'ns/logical byte'
        svg=[f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1040 {height}" role="img">',
             f'<title>{html.escape(case)}: medians and interquartile ranges, {unit}, logarithmic axis</title>',
             '<rect width="100%" height="100%" fill="white"/>',
             '<style>text{font:14px system-ui;fill:#26333a}</style>',
             f'<text x="20" y="28">{html.escape(case)} · median and IQR · {unit} · logarithmic axis</text>']
        for power in range(lo,hi+1):
            pos=x(10**power)
            svg += [f'<path d="M {pos} 50 V {height-45}" stroke="#e4e9e9"/>',
                    f'<text x="{pos}" y="{height-20}" text-anchor="middle">{10**power:g}</text>']
        for gi,n in enumerate(groups):
            y=80+gi*90
            svg.append(f'<text x="20" y="{y}">{n:,} '+('key bytes' if case.startswith('key_') else 'bytes')+'</text>')
            for ii,impl in enumerate(('CJR','OpenSSL')):
                r=next(r for r in rows if r['n']==n and r['implementation']==impl)
                cy=y+ii*27
                color=('#176f76','#de8b37')[ii]
                svg += [f'<path d="M {x(r["q1_ns"])} {cy} H {x(r["q3_ns"])}" stroke="{color}" stroke-width="5"/>',
                        f'<circle cx="{x(r["median_ns"])}" cy="{cy}" r="5" fill="{color}"/>',
                        f'<text x="830" y="{cy+5}">{impl}: {r["median_ns"]:.2f}</text>']
        svg.append('</svg>')
        (output/f'{case}.svg').write_text('\n'.join(svg)+'\n')
    paired={(r['case'],r['n'],r['implementation']):r for r in data}
    ratios=[dict(case=r['case'],n=r['n'],cjr_median_ns=r['median_ns'],
                 openssl_median_ns=paired[r['case'],r['n'],'OpenSSL']['median_ns'],
                 cjr_over_openssl=r['median_ns']/paired[r['case'],r['n'],'OpenSSL']['median_ns'])
            for r in data if r['implementation']=='CJR']
    (output/'comparison.json').write_text(json.dumps(ratios,indent=2)+'\n')
if __name__=='__main__': main()
