#!/usr/bin/env python3
"""Check local HTML destinations and anchors, including API→Rocq links."""
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit


class Page(HTMLParser):
    def __init__(self):
        super().__init__()
        self.ids=set()
        self.links=[]

    def handle_starttag(self,tag,attrs):
        attributes=dict(attrs)
        if 'id' in attributes:
            self.ids.add(attributes['id'])
        if tag=='a' and 'href' in attributes:
            self.links.append(attributes['href'])


def main():
    root=Path(__file__).resolve().parents[1]/'docs'
    pages={}
    for path in root.rglob('*.html'):
        parsed=Page()
        parsed.feed(path.read_text())
        pages[path.resolve()]=parsed
    errors=[]
    checked=0
    for path,page in pages.items():
        for link in page.links:
            url=urlsplit(link)
            if url.scheme or url.netloc:
                continue
            target=(path.parent/unquote(url.path)).resolve() if url.path else path
            if target.suffix!='.html':
                continue
            checked+=1
            if target not in pages or (url.fragment and unquote(url.fragment) not in pages[target].ids):
                errors.append((str(path.relative_to(root)),link))
    if errors:
        raise RuntimeError(f'{len(errors)} broken HTML links: {errors[:20]}')
    print(f'Documentation: {len(pages)} pages, {checked} local HTML links and anchors checked.')


if __name__=='__main__':
    main()
