"""Unaligned-key (KU) copies of root's set/insert chain."""
import re, os, sys, json
R = '/home/zksecurity/trim-space/init-e/work/finite-auth-checkout/submission/InitECandidate/Runtime'
S = '/tmp/claude-1000/-home-zksecurity-trim-space-init-e-work-finite-auth-checkout/7ae2074a-31c1-4ec7-aa8e-0153dccd0194/scratchpad'
STRUCTS = {'HashInsertCopyBounds': 'HashInsertProbeTail'}
LEAVES = ['HashTableArraysInvariant.find_supported', 'evaluate_hash_supported_declaration',
          'evaluate_memcpy_aligned_call_with_frame']
cp = [l.split() for l in open(S + '/meta/ku_list.txt') if l.strip()]
byf = {}
for n, m in cp:
    byf.setdefault(m, set()).add(n)
for st, m in STRUCTS.items():
    byf.setdefault(m, set()).add(st)
names = set(n for n, _ in cp) | set(LEAVES)

def newname(n):
    p = n.split('.')
    if p[0] in STRUCTS:
        return '.'.join([p[0] + 'KU'] + p[1:])
    p[-1] = p[-1] + 'KU'
    return '.'.join(p)

def imports(f):
    return re.findall(r'^import InitECandidate\.Runtime\.(\S+)', open(R + '/' + f + '.lean').read(), re.M)

order = []; seen = set()
sys.setrecursionlimit(100000)
def vis(f):
    if f in seen: return
    seen.add(f)
    if not os.path.exists(R + '/' + f + '.lean'): return
    for i in imports(f): vis(i)
    if f in byf: order.append(f)
for f in sorted(byf): vis(f)

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |noncomputable |protected )*(theorem|lemma|def|abbrev|structure|inductive|instance)\s+([^\s({:]+)')
dotlast = {}
for n in names:
    p = n.split('.')
    if len(p) > 1 and p[0] not in STRUCTS:
        dotlast[p[-1]] = p[-1] + 'KU'
plain = sorted([n for n in names if n.split('.')[0] not in STRUCTS], key=len, reverse=True)

def rename(t):
    for st in STRUCTS:
        t = re.sub(r'(?<![\w.\'])' + re.escape(st) + r'(?![\w\'])', st + 'KU', t)
    for n in plain:
        t = re.sub(r'(?<![\w.\'])' + re.escape(n) + r'(?![\w\'])', newname(n), t)
    for a, b in dotlast.items():
        t = re.sub(r'(?<=[\w)\]])\.' + re.escape(a) + r'(?![\w\'])', '.' + b, t)
    return t

def rules(t):
    for h in ('keyAligned', 'sourceAligned'):
        t = t.replace('(%s : key.toNat %% 8 = 0)' % h,
                      '(%s : key.toNat %% 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)' % h)
    t = t.replace('  sourceAligned : key.toNat % 8 = 0\n',
                  '  sourceAligned : key.toNat % 8 ≠ 0\n  len8 : 8 ≤ keyLength.toNat\n  keyFit : key.toNat + keyLength.toNat ≤ 33806089496\n')
    # passing the alignment fact passes the two new facts too
    t = re.sub(r'(?<![\w.\'])((?:\w+\.)*)(keyAligned|sourceAligned)(?![\w\'])(?!\s*:)(?! :=)',
               lambda m: '%s%s %slen8 %skeyFit' % (m.group(1), m.group(2), m.group(1), m.group(1)), t)
    t = re.sub(r'([⟨,])((?:\w+\.)*)(keyAligned|sourceAligned) \2len8 \2keyFit(?=[,⟩])', r'\1\2\3,\2len8,\2keyFit', t)
    def _bud(line):
        if re.search(r'(\(capacity \* \(?2[^)]*\)?\)\.toNat|capacity\.toNat \* 2) = [0-9]+ \* capacity\.toNat', line): return line
        return line.replace('2 * capacity.toNat', '54 * capacity.toNat').replace('3 * capacity.toNat', '55 * capacity.toNat')
    t = '\n'.join(_bud(l) for l in t.split('\n'))
    return t

def gen(f):
    hand = S + '/kuhand/' + f + 'KU.lean'
    if os.path.exists(hand):
        open(R + '/' + f + 'KU.lean', 'w').write(open(hand).read()); return
    lines = open(R + '/' + f + '.lean').read().split('\n')
    keep = byf[f]
    out = []; i = 0; n = len(lines); pend = []
    def flush(k):
        nonlocal pend
        if k: out.extend(pend)
        pend = []
    while i < n:
        l = lines[i]
        if l.startswith('/--'):
            j = i
            while '-/' not in lines[j]: j += 1
            pend.extend(lines[i:j + 1]); i = j + 1; continue
        if l.startswith('/-!'):
            j = i
            while '-/' not in lines[j]: j += 1
            i = j + 1; continue
        m = DECL.match(l)
        if m:
            nm = m.group(2)
            j = i + 1
            while j < n and (lines[j].startswith(' ') or lines[j].startswith('\t') or
                             (lines[j] == '' and j + 1 < n and (lines[j + 1].startswith(' ') or lines[j + 1].startswith('\t')))):
                j += 1
            if nm in keep:
                flush(True); out.extend(lines[i:j])
            else:
                flush(False)
            i = j; continue
        if pend: flush(True)
        if l.startswith('#print axioms'):
            if l.split()[-1] in keep: out.append(l)
            i += 1; continue
        if l.startswith('import ') or l.startswith('set_option max'):
            i += 1; continue
        out.append(l); i += 1
    t = '\n'.join(out)
    t = rules(t)
    t = rename(t)
    import importlib.util
    spec = importlib.util.spec_from_file_location('kufix', S + '/kufix.py'); fx = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(fx)
    for old, new in fx.FIX.get(f, []):
        if old not in t: print('FIXMISS', f, old[:60].replace('\n', ' '))
        t = t.replace(old, new)
    imps = [f, 'PtKeyULeafKUGD']
    tc = set(); st = list(imports(f))
    while st:
        x = st.pop()
        if x in tc or not os.path.exists(R + '/' + x + '.lean'): continue
        tc.add(x); st.extend(imports(x))
    for g in order:
        if g in tc and g != f:
            imps.append(g + 'KU')
    hdr = '\n'.join('import InitECandidate.Runtime.' + x for x in imps) + '\n'
    hdr += '/-! Unaligned-key copy of `%s` (generated; see PtKeyULeafKUGD): key alignment replaced by `key %% 8 ≠ 0`, `8 ≤ keyLength`\nand the key fit; lookup budgets made linear in the width bound (`54·cap`). -/\n' % f
    open(R + '/' + f + 'KU.lean', 'w').write(hdr + t.lstrip('\n'))

if __name__ == '__main__':
    only = sys.argv[1:]
    json.dump(order, open(S + '/meta/ku_order.json', 'w'))
    for f in order:
        if only and f not in only: continue
        gen(f)
    print(len(order), 'modules')
