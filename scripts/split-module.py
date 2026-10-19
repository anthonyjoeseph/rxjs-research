#!/usr/bin/env python3
"""Split one Agda module into contiguous parts and retarget its consumers.

Textual and approximate by design: it gets a split most of the way, and the
typechecker plus `make imports-fix` finish it.  See docs/split.md.

  split-module.py FILE --cuts                     list where it may be cut
  split-module.py FILE [--dry] PART PART ...      split it

PART is `MOD@LINE` (the first part takes no `@LINE`).  When the file is one
parametrised module wrapping everything (`module W (R : Set) where`), give
each part a wrapper name too: `MOD:WRAPPER@LINE`.  LINE is the ORIGINAL
file's line where the part begins (a leading comment block included).
"""
import os
import re
import sys

ROOT = os.path.abspath(os.environ.get('SPLIT_ROOT') or os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'agda-impl'))
KW = {'mutual', 'postulate', 'abstract', 'instance', 'private', 'field', 'opaque'}
TOK = re.compile(r'[\s(){};"@]+')


def code_at(l, d):
    """A declaration starting at indent `d`."""
    return (len(l) > d and l[:d].strip() == '' and not l[d].isspace()
            and not l[d:].startswith('--') and not l[d:].startswith('{-'))


def header_end(src, modline):
    """End of the run of import/open lines after the module line."""
    end = modline + 1
    i = modline + 1
    while i < len(src):
        l = src[i]
        if not l.strip() or l.startswith('--'):
            i += 1
            continue
        if code_at(l, 0) and re.match(r'(open import|import) ', l):
            i += 1
            while i < len(src) and src[i][:1].isspace():
                i += 1
            end = i
            continue
        break
    return end


def wrapper(src, start):
    """The single top-level parametrised module after `start`, if any."""
    tops = [i for i in range(start, len(src)) if code_at(src[i], 0)]
    mods = [i for i in tops if src[i].startswith('module ') and src[i].rstrip().endswith('where')]
    if mods and all(not code_at(src[j], 0) for j in range(mods[-1] + 1, len(src))):
        return mods[-1]
    return None


def cut_points(lines, lo, hi, d):
    """Lines in [lo, hi) where a cut at indent `d` splits no definition."""
    occ = [(lines[i][d:].split()[0], i) for i in range(lo, hi) if code_at(lines[i], d)]
    sigs = {t for t, i in occ if re.match(r'\s*' + re.escape(t) + r'\s+:(\s|$)', lines[i])}
    first, last = {}, {}
    for t, i in occ:
        if t in sigs:
            first.setdefault(t, i)
            last[t] = i
    keys = KW | {'module', 'data', 'record', 'open', 'infix', 'infixl', 'infixr'}
    out = []
    prev = None
    for t, i in occ:
        ok = (t in sigs or t in keys) and not any(first[x] < i <= last[x] for x in first)
        if prev is not None and lines[prev][d:].startswith('{-#'):
            ok = False
        prev = i
        if not ok:
            continue
        j = i
        while j - 1 >= lo and lines[j - 1][:d].strip() == '' and lines[j - 1][d:].startswith('--'):
            j -= 1
        out.append(j)
    return out


def exports(body):
    """Names a block of declarations (at indent 0) exports, and its privates."""
    out, priv, fields = set(), set(), {}
    stack = []
    for l in body:
        if not l.strip() or l.lstrip().startswith(('--', '{-')):
            continue
        d = len(l) - len(l.lstrip())
        while stack and stack[-1][0] >= d:
            stack.pop()
        s = l.strip()
        kinds = [k for (_, k, _) in stack]
        hidden = any(k in ('opaque', 'module') for k in kinds)
        tgt = priv if 'private' in kinds else out
        ctx = kinds[-1] if kinds else 'top'
        w = s.split()
        first = w[0]
        kind, nm = None, None
        if first in KW and len(w) == 1:
            kind = first
        elif first == 'field' and ctx == 'record':
            # `field x : T` opens a field block too: the names under it are fields
            kind = 'field'
        elif first == 'interleaved' and 'mutual' in w:
            kind = 'mutual'
        elif first == 'module' and len(w) > 1 and w[1] == '_':
            kind = 'anon'
        elif first in ('data', 'record', 'module') and len(w) > 1:
            nm = w[1]
            kind = first if (first == 'module' or s.endswith('where')) else None
        elif s.endswith(' where') or first == 'where':
            kind = 'opaque'
        rec = [n for (_, k, n) in stack if k == 'record']
        if not hidden:
            if nm:
                tgt.add(nm)
            elif first == 'pattern' and len(w) > 1:
                tgt.add(w[1])
            elif ctx == 'record' and first == 'constructor':
                tgt.add(w[1])
            elif ctx == 'record' and first == 'field' and len(w) > 1:
                m = re.match(r'field\s+(.+?)\s+:(\s|$)', s)
                if m and rec:
                    fields.setdefault(rec[-1], set()).update(m.group(1).split())
            elif ctx == 'field':
                m = re.match(r'(.+?)\s+:(\s|$)', s)
                if m and rec:
                    fields.setdefault(rec[-1], set()).update(m.group(1).split())
            elif ctx in ('top', 'mutual', 'postulate', 'abstract', 'instance', 'private', 'data', 'anon'):
                m = re.match(r'(.+?)\s+:(\s|$)', s)
                if m and first not in ('open', 'import', 'syntax', '...', '|', 'where') and not first.startswith(('infix', '{-#')):
                    names = m.group(1).split()
                    if all(re.match(r'^[^\s(){}.;]+$', x) for x in names):
                        tgt.update(names)
            if first == 'open' and s.endswith('public') and len(w) > 1:
                tgt.update(fields.get(w[1], set()))
        if kind:
            stack.append((d, kind, nm))
    return out, priv


def tokens(lines):
    t = set()
    for l in lines:
        for w in TOK.split(re.sub(r'--.*$', '', l)):
            if w:
                t.add(w)
                t.update(p for p in w.split('.') if p)
    return t


def uses(toks, names):
    """The names a token set mentions; a mixfix `_<ᵖ_` by all its parts."""
    return {n for n in names
            if n in toks or ('_' in n and all(x in toks for x in n.split('_') if x) and any(n.split('_')))}


def mod_names(body):
    return {m.group(1) for l in body for m in [re.match(r'^module (\S+)', l)] if m}


def args_of(params):
    """Explicit binder names of a module telescope: `(R : Set) {A} (x y : T)`."""
    out = []
    for m in re.finditer(r'\(([^():]+):', params):
        out += m.group(1).split()
    return ' '.join(out)


def path_of(mod):
    return os.path.join(ROOT, *mod.split('.')) + '.agda'


def clause_at(txt, i):
    """A possibly multi-line declaration starting at line i: (text, end)."""
    d = len(txt[i]) - len(txt[i].lstrip())
    j = i + 1
    while j < len(txt) and txt[j].strip() and (len(txt[j]) - len(txt[j].lstrip())) > d \
            and not txt[j].lstrip().startswith('--'):
        j += 1
    return ' '.join(x.strip() for x in txt[i:j]), j


def split_items(rest):
    um = re.search(r'using \(([^)]*)\)', rest)
    rm = re.search(r'renaming \(([^)]*)\)', rest)
    other = re.sub(r'using \([^)]*\)|renaming \([^)]*\)', '', rest).strip()
    us = [x.strip() for x in um.group(1).split(';') if x.strip()] if um else []
    # Agda allows several `renaming (…)` groups on one clause
    rs = [x.strip() for g in re.findall(r'renaming \(([^)]*)\)', rest) for x in g.split(';') if x.strip()]
    return um, rm, other, us, rs


def bucket(us, rs, owner, where, problems):
    b = {}
    for it in us:
        nm = it.split()[-1]
        hs = owner(nm)
        if not hs:
            problems.append(f'{where}: nothing owns `{nm}`')
        for h in hs:
            b.setdefault(h, ([], []))[0].append(it)
    for it in rs:
        nm = it.split(' to ')[0].split()[-1]
        hs = owner(nm)
        if not hs:
            problems.append(f'{where}: nothing owns renamed `{nm}`')
        for h in hs:
            b.setdefault(h, ([], []))[1].append(it)
    return b


def render(head, us, rs):
    s = head
    if us or rs:
        s += ' using (' + '; '.join(us) + ')'
    if rs:
        s += ' renaming (' + '; '.join(rs) + ')'
    return s


def split_sub(path, name, spec, dry):
    """Split nested module `name` in place: from LINE on, a sibling `new`
    with the same telescope, opening `name`.  Consumers retargeted."""
    new, _, line = spec.partition('@')
    cut = int(line) - 1
    src = open(path).read().split('\n')
    ml = [i for i, l in enumerate(src) if re.match(r'\s*module ' + re.escape(name) + r'\s.*where\s*$', l)]
    if len(ml) != 1:
        sys.exit(f'need exactly one `module {name} … where`, found {len(ml)}')
    ml = ml[0]
    d = len(src[ml]) - len(src[ml].lstrip())
    tel = re.match(r'\s*module \S+\s*(.*?)\s*where\s*$', src[ml]).group(1)
    args = args_of(tel)
    end = ml + 1
    while end < len(src) and not (src[end].strip() and len(src[end]) - len(src[end].lstrip()) <= d
                                  and not src[end].lstrip().startswith('--')):
        end += 1
    if not ml < cut < end or cut not in cut_points(src, ml + 1, end, d + 2):
        sys.exit(f'line {line} is not a cut inside `{name}` (lines {ml + 2}-{end}); '
                 f'cuts: {[c + 1 for c in cut_points(src, ml + 1, end, d + 2)]}')
    pre = []
    i = ml + 1
    while i < cut:
        l = src[i]
        if not l.strip() or l.lstrip().startswith('--'):
            i += 1
            continue
        if code_at(l, d + 2) and re.match(r'\s*open ', l):
            c, i = clause_at(src, i)
            pre.append(' ' * (d + 2) + c)
            continue
        break
    two = [l[d + 2:] for l in src[cut:end]]
    o2, _ = exports(two)
    o1, p1 = exports([l[d + 2:] for l in src[ml + 1:cut]])
    problems = [f'`{b}` is private in `{name}` and used after the cut' for b in sorted(tokens(two) & p1)]
    ind = ' ' * d
    src = src[:cut] + ['', f'{ind}module {new} {tel} where'.replace('  where', ' where'),
                       f'{ind}  open {name} {args}'] + pre + [''] + src[cut:]

    changes = {path: src}
    for dp, _, fns in os.walk(ROOT):
        if '_build' in dp or '_cli' in dp:
            continue
        for fn in fns:
            p = os.path.join(dp, fn)
            if fn.endswith('.agda') and p != path:
                t = open(p).read()
                if re.search(r'\bmodule ' + re.escape(name) + r'\b', t):
                    changes[p] = t.split('\n')
    owner2 = lambda n: [1] if n in o2 else [0] if n in o1 else []
    for p, txt in changes.items():
        rel = os.path.relpath(p, ROOT)
        text = '\n'.join(txt)
        # how this file names the module: itself, or renamed on import
        handles = {name: new}
        for m in re.finditer(r'\bmodule ' + re.escape(name) + r' to (\S+?)(?=\s*[;)])', text):
            handles[m.group(1)] = m.group(1) + '′'
            if not re.search(r'\bmodule ' + re.escape(name) + r'\s*[;)]', text):
                del handles[name]
        text = re.sub(r'\bmodule ' + re.escape(name) + r' to (\S+?)(?=\s*[;)])',
                      lambda m: f'module {name} to {m.group(1)}; module {new} to {m.group(1)}′', text)
        text = re.sub(r'\bmodule ' + re.escape(name) + r'(?=\s*[;)])', f'module {name}; module {new}', text)
        txt = text.split('\n')
        out, i = [], 0
        while i < len(txt):
            l = txt[i]
            if p == path and (i == ml or l.strip() == f'open {name} {args}'):
                out.append(l)
                i += 1
                continue
            hit = False
            for h, h2 in list(handles.items()):
                m = re.match(r'^(\s*)module (\S+) = ' + re.escape(h) + r'\b(.*)$', l)
                if m:
                    handles[m.group(2)] = m.group(2) + '′'
                    out += [l, f'{m.group(1)}module {m.group(2)}′ = {h2}{m.group(3)}']
                    i += 1
                    hit = True
                    break
                m = re.match(r'^(\s*)open ' + re.escape(h) + r' (.*)$', l)
                if m:
                    clause, j = clause_at(txt, i)
                    body = clause.split(' ', 2)[2]
                    cm = re.search(r'\b(using|renaming|hiding|public)\b', body)
                    a = body[:cm.start()].strip() if cm else body.strip()
                    um, rm, other, us, rs = split_items(body[cm.start():] if cm else '')
                    if not (um or rm) and not other:
                        out += txt[i:j] + [f'{m.group(1)}open {h2} {a}']
                    elif other:
                        problems.append(f'{rel}: cannot retarget `{clause}`')
                        out += txt[i:j]
                    else:
                        b = bucket(us, rs, owner2, rel, problems)
                        for k, (bu, br) in sorted(b.items()):
                            out.append(m.group(1) + render(f'open {[h, h2][k]} {a}', bu, br))
                    i = j
                    hit = True
                    break
            if not hit:
                out.append(l)
                i += 1
        text = '\n'.join(out)
        for h, h2 in handles.items():
            text = re.sub(r'(?<![\w.])' + re.escape(h) + r'\.([^\s(){};.]+)',
                          lambda m: (f'{h2}.{m.group(1)}' if m.group(1) in o2 and m.group(1) not in o1
                                     else m.group(0)), text)
        changes[p] = text
    print(f'`{name}` cut at {line}: `{new}` takes {len(o2)} name(s); {len(changes) - 1} consumer file(s) touched')
    for pr in problems:
        print('PROBLEM', pr)
    if not dry:
        for p, t in changes.items():
            open(p, 'w').write(t if isinstance(t, str) else '\n'.join(t))


def main():
    argv = sys.argv[1:]
    dry = '--dry' in argv
    cuts = '--cuts' in argv
    if '--sub' in argv:
        k = argv.index('--sub')
        split_sub(os.path.abspath(argv[0]), argv[k + 1], argv[k + 2], dry)
        return
    argv = [a for a in argv if a not in ('--dry', '--cuts')]
    path = os.path.abspath(argv[0])
    src = open(path).read().split('\n')
    if src and src[-1] == '':
        src.pop()
    modline = next(i for i, l in enumerate(src) if l.startswith('module '))
    orig = src[modline].split()[1]
    hend = header_end(src, modline)
    wl = wrapper(src, hend)

    if cuts:
        if wl is not None:
            lo = wl + 1
            while lo < len(src) and not (code_at(src[lo], 2) and not re.match(r'\s*(open |module \S+ = )', src[lo])):
                lo += 1
            pts, d = cut_points(src, lo, len(src), 2), 2
            print(f'{orig}: {len(src)} lines, wrapper `{src[wl].split()[1]}` at {wl + 1}; cuts at indent 2')
        else:
            pts, d = cut_points(src, hend, len(src), 0), 0
            print(f'{orig}: {len(src)} lines; cuts at indent 0')
        prev = None
        for p in pts:
            gap = '' if prev is None else f'  (+{p - prev})'
            print(f'{p + 1:6}{gap:10} {src[p][:90]}')
            prev = p
        return

    specs = []
    for k, a in enumerate(argv[1:]):
        name, _, line = a.partition('@')
        mod, _, wrap = name.partition(':')
        specs.append((mod, wrap or None, int(line) - 1 if line else None))
    inner = specs[0][1] is not None
    if inner and wl is None:
        sys.exit('wrapper names given, but the file is not one parametrised module')

    problems = []
    header_comment = src[:modline]
    header_imports = src[modline + 1:hend]
    if inner:
        wname = src[wl].split()[1]
        params = re.match(r'module \S+\s*(.*?)\s*where\s*$', src[wl]).group(1)
        args = args_of(params)
        prelude = src[hend:wl]
        local_opens = [l for l in prelude if code_at(l, 0) and l.startswith('open ')]
        prelude_defs = [l for l in prelude if l not in local_opens]
        i = wl + 1
        pre_end = i
        while i < len(src):
            l = src[i]
            if not l.strip() or l.lstrip().startswith('--'):
                i += 1
                continue
            if code_at(l, 2) and re.match(r'\s*(open |module \S+ = |import )', l):
                _, i = clause_at(src, i)
                pre_end = i
                continue
            break
        inner_pre = src[wl + 1:pre_end]
        first_body = pre_end
    else:
        local_opens, prelude_defs, inner_pre = [], [], []
        first_body = hend

    starts = [s if s is not None else first_body for (_, _, s) in specs]
    parts = []
    for k, (mod, wrap, _) in enumerate(specs):
        st = starts[k]
        en = starts[k + 1] if k + 1 < len(specs) else len(src)
        body = src[st:en]
        while body and not body[0].strip():
            body.pop(0)
        flat = [l[2:] if inner else l for l in body]
        o, p = exports(flat)
        parts.append(dict(mod=mod, wrap=wrap, body=body, flat=flat, out=o, priv=p, mods=mod_names(flat)))
    pexp, ppriv = exports(prelude_defs) if inner else (set(), set())

    files = {}
    for k, pt in enumerate(parts):
        used = tokens(pt['body']) - pt['out'] - pt['priv']
        options = [l for l in header_comment if l.startswith('{-# OPTIONS')]
        # the header's prose stays with the original name, else the first part
        keeps = pt['mod'] == orig if any(q['mod'] == orig for q in parts) else k == 0
        lines = (header_comment if keeps else options + ([''] if options else [])) + [f'module {pt["mod"]} where'] + header_imports
        inner_imps, file_imps, rec_opens = [], [], []
        for j in range(k):
            q = parts[j]
            # a bare `open R` in an earlier part brings R's fields here too
            recs = [l.split()[1] for l in q['flat'] if re.match(r'open \S+$', l)]
            rec_opens += [f'open {r}' for r in recs if f'open {r}' not in rec_opens]
            names = sorted(uses(used | set(recs), q['out']))
            for b in sorted(uses(used, q['priv'])):
                problems.append(f'{pt["mod"]} uses `{b}`, private in {q["mod"]}')
            if not names:
                continue
            items = [('module ' + x) if x in q['mods'] else x for x in names]
            if inner:
                file_imps.append((q['mod'], ['module ' + q['wrap']]))
                inner_imps.append(f'  open {q["wrap"]} {args} using ({"; ".join(items)})'.replace('  ', '  ', 1))
            else:
                file_imps.append((q['mod'], items))
        if inner and k > 0:
            pn = sorted(uses(tokens(pt['body']) | tokens(inner_pre), pexp))
            if pn:
                file_imps.insert(0, (parts[0]['mod'], pn))
        merged = {}
        for m, items in file_imps:
            merged.setdefault(m, [])
            merged[m] += [x for x in items if x not in merged[m]]
        for m, items in merged.items():
            lines.append(f'open import {m} using ({"; ".join(items)})')
        if inner:
            lines += local_opens + [''] + (prelude_defs if k == 0 else [])
            lines.append(f'module {pt["wrap"]} {params} where'.replace('  ', ' '))
            lines += inner_pre + inner_imps + ['  ' + o for o in rec_opens] + ['']
        else:
            lines += [''] + rec_opens + ([''] if rec_opens else [])
        lines += pt['body']
        files[path_of(pt['mod'])] = '\n'.join(lines).rstrip('\n') + '\n'

    def owner(nm):
        return [k for k, pt in enumerate(parts) if nm in pt['out']]

    def owner_mod(nm):
        if inner and nm == wname:
            return []
        if inner and nm in pexp:
            return [0]
        return owner(nm)

    file_re = re.compile(r'^(open import|import) ' + re.escape(orig) + r'(\s|$)')
    wrap_re = re.compile(r'^(\s*)open ' + re.escape(wname) + r'(\.\S+)? (.*)$') if inner else None
    changes = {}
    for dp, _, fns in os.walk(ROOT):
        if '_build' in dp or '_cli' in dp:
            continue
        for fn in fns:
            p = os.path.join(dp, fn)
            if not fn.endswith('.agda') or os.path.abspath(p) == path:
                continue
            txt = open(p).read().split('\n')
            if not any(file_re.match(l) for l in txt):
                continue
            rel = os.path.relpath(p, ROOT)
            out, i, changed = [], 0, False
            # inner opens first, so the file import knows which wrappers live
            while i < len(txt):
                m = wrap_re.match(txt[i]) if inner else None
                if not m:
                    out.append(txt[i])
                    i += 1
                    continue
                clause, j = clause_at(txt, i)
                ind = m.group(1)
                sub = (m.group(2) or '')[1:]
                body = clause.split(' ', 2)[2]
                cut = re.search(r'\b(using|renaming|hiding|public)\b', body)
                a = body[:cut.start()].strip() if cut else body.strip()
                um, rm, other, us, rs = split_items(body[cut.start():] if cut else '')
                if sub:
                    hs = owner(sub.split('.')[0])
                    if len(hs) != 1:
                        problems.append(f'{rel}: cannot place `{wname}.{sub}`')
                        out += txt[i:j]
                    else:
                        out.append(ind + clause.replace(f'open {wname}.', f'open {parts[hs[0]]["wrap"]}.', 1))
                        changed = True
                    i = j
                    continue
                hm = re.match(r'hiding \(([^)]*)\)$', other)
                if not (um or rm) and (not other or hm):
                    # blanket, or hiding: every part opened, each hiding its own
                    hid = [x.strip() for x in hm.group(1).split(';') if x.strip()] if hm else []
                    for k, pt in enumerate(parts):
                        mine = [x for x in hid if k in owner(x.split()[-1])]
                        out.append(ind + f'open {pt["wrap"]} {a}' + (f' hiding ({"; ".join(mine)})' if mine else ''))
                    changed = True
                    i = j
                    continue
                if other or not (um or rm):
                    problems.append(f'{rel}: cannot retarget `{clause}`')
                    out += txt[i:j]
                    i = j
                    continue
                b = bucket(us, rs, owner, rel, problems)
                if list(b) == [0] and parts[0]['wrap'] == wname:
                    out += txt[i:j]
                    i = j
                    continue
                for h, (bu, br) in sorted(b.items()):
                    out.append(ind + render(f'open {parts[h]["wrap"]} {a}', bu, br))
                changed = True
                i = j
            txt, out, i = out, [], 0
            if inner:
                def qual(m):
                    hs = owner(m.group(1))
                    if len(hs) != 1:
                        problems.append(f'{rel}: cannot place `{wname}.{m.group(1)}`')
                        return m.group(0)
                    return f'{parts[hs[0]]["wrap"]}.{m.group(1)}'
                q_re = re.compile(r'(?<![\w.])' + re.escape(wname) + r'\.([^\s(){};.]+)')
                for n, l in enumerate(txt):
                    if not file_re.match(l):
                        l2 = q_re.sub(qual, l)
                        changed |= l2 != l
                        txt[n] = l2
                for l in ([] if any(pt['wrap'] == wname for pt in parts) else txt):
                    if re.search(r'(?<![\w.])' + re.escape(wname) + r'(?![\w.])', l) and not file_re.match(l):
                        problems.append(f'{rel}: other use of `{wname}`: {l.strip()}')
            while i < len(txt):
                if not file_re.match(txt[i]):
                    out.append(txt[i])
                    i += 1
                    continue
                clause, j = clause_at(txt, i)
                head = clause.split()[0]
                m = re.match(r'^(open import|import) \S+\s*(.*)$', clause)
                um, rm, other, us, rs = split_items(m.group(2))
                am = re.match(r'as (\S+)$', other)
                if head == 'import' and am and not (um or rm):
                    # qualified: part k gets alias Q, Q′, Q″…; each `Q.name` follows its owner
                    q = am.group(1)
                    alias = lambda k: q + '′' * k
                    seen = set()

                    def requal(mm):
                        hs = owner_mod(mm.group(1))
                        if len(hs) != 1:
                            problems.append(f'{rel}: cannot place `{q}.{mm.group(1)}`')
                            return mm.group(0)
                        seen.add(hs[0])
                        return f'{alias(hs[0])}.{mm.group(1)}'
                    qq = re.compile(r'(?<![\w.])' + re.escape(q) + r'\.([^\s(){};.]+)')
                    txt[j:] = [qq.sub(requal, l) for l in txt[j:]]
                    out += [f'import {parts[k]["mod"]} as {alias(k)}' for k in sorted(seen)]
                    changed = True
                    i = j
                    continue
                if head != 'open' or other or not (um or rm):
                    problems.append(f'{rel}: cannot retarget `{clause}`')
                    out += txt[i:j]
                    i = j
                    continue
                rest = '\n'.join(txt)
                keep_us = []
                for it in us:
                    if inner and it == f'module {wname}':
                        for pt in parts:
                            if re.search(r'(?<![\w.])' + re.escape(pt['wrap']) + r'[ .]', rest):
                                keep_us.append(f'module {pt["wrap"]}')
                    else:
                        keep_us.append(it)
                wraps = {f'module {pt["wrap"]}': k for k, pt in enumerate(parts)} if inner else {}
                b = {}
                for it in keep_us:
                    if it in wraps:
                        b.setdefault(wraps[it], ([], []))[0].append(it)
                for h, (bu, br) in bucket([x for x in keep_us if x not in wraps], rs, owner_mod, rel, problems).items():
                    e = b.setdefault(h, ([], []))
                    e[0].extend(bu)
                    e[1].extend(br)
                if list(b) == [0] and parts[0]['mod'] == orig and keep_us == us:
                    out += txt[i:j]
                    i = j
                    continue
                for h, (bu, br) in sorted(b.items()):
                    out.append(render(f'open import {parts[h]["mod"]}', bu, br))
                changed = True
                i = j
            if inner:
                for l in out:
                    m = re.search(r'module (\S+) = ' + re.escape(wname) + r'\b', l)
                    if m:
                        problems.append(f'{rel}: alias `{m.group(1)}` of `{wname}`: its uses are not retargeted')
            if changed:
                changes[p] = '\n'.join(out)

    for pt, (fp, t) in zip(parts, files.items()):
        print(f'{pt["mod"]}: {t.count(chr(10))} lines')
    print(f'{len(changes)} consumer(s) retargeted')
    for pr in problems:
        print('PROBLEM', pr)
    if not dry:
        os.remove(path)
        for fp, t in files.items():
            os.makedirs(os.path.dirname(fp), exist_ok=True)
            open(fp, 'w').write(t)
        for fp, t in changes.items():
            open(fp, 'w').write(t)
        print('next: make imports-fix, then make agda')


if __name__ == '__main__':
    try:
        main()
    except BrokenPipeError:
        pass
