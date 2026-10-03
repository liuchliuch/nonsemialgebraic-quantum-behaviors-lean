#!/usr/bin/env python3
"""Check source hygiene, complete imports, and the independent specification boundary."""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]

def lean_code(text):
    """Discard nested block comments, line comments and strings before token checks."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            i += 1
            out.append(' "" ')
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError('Unclosed block comment')
    return ''.join(out)

files = [ROOT / 'QuantumBehaviors.lean', *sorted((ROOT / 'QuantumBehaviors').rglob('*.lean')),
         ROOT / 'Verification/Solution.lean']
modules = {str(p.relative_to(ROOT)).removesuffix('.lean').replace('/', '.'): p for p in files}
imports = {}
for name, path in modules.items():
    code = lean_code(path.read_text())
    forbidden = re.search(r'\b(sorry|admit|axiom|native_decide|implemented_by|unsafe|extern)\b', code)
    if forbidden:
        raise SystemExit(f'{path.relative_to(ROOT)}: forbidden token {forbidden[0]}')
    imports[name] = re.findall(r'^(?:public\s+)?import\s+([\w.]+)', code, re.M)

def closure(start):
    visited, todo = set(), list(start)
    while todo:
        name = todo.pop()
        if name in visited:
            continue
        visited.add(name)
        todo.extend(m for m in imports.get(name, []) if m.startswith('QuantumBehaviors'))
    return visited

library = {m for m in modules if m.startswith('QuantumBehaviors')}
missing = library - closure(['QuantumBehaviors'])
if missing:
    raise SystemExit(f'Unreachable library modules: {sorted(missing)}')
challenge = (ROOT / 'Verification/Challenge.lean').read_text()
solution = (ROOT / 'Verification/Solution.lean').read_text()
trusted = {
    'QuantumBehaviors.Definitions', 'QuantumBehaviors.Scenarios.Definitions',
    'QuantumBehaviors.Dimension.Definitions', 'QuantumBehaviors.LiftDefinitions',
    'QuantumBehaviors.POVM.Definitions', 'QuantumBehaviors.NPA.Definitions',
    'QuantumBehaviors.NPA.Words', 'QuantumBehaviors.AlmostQuantum.Definitions',
}
challenge_imports = re.findall(r'^import\s+(QuantumBehaviors[\w.]*)', challenge, re.M)
if closure(challenge_imports) - trusted:
    raise SystemExit('Challenge imports project implementation proofs outside its review boundary')
pattern = r'\btheorem\s+(\w+)\s*:(.*?)\s*:='
def signatures(text):
    return [(n, ' '.join(s.split())) for n, s in re.findall(pattern, lean_code(text), re.S)]
a, b = signatures(challenge), signatures(solution)
if a != b or not a:
    raise SystemExit('Challenge/Solution source signatures do not match')
config = json.loads((ROOT / 'Verification/comparator.json').read_text())
if config['theorem_names'] != ['PaperChecks.' + n for n, _ in a]:
    raise SystemExit('Comparator does not cover exactly the declared paper checks')
if set(config['permitted_axioms']) != {'propext', 'Quot.sound', 'Classical.choice'}:
    raise SystemExit('Unexpected Comparator axiom whitelist')
for path in ROOT.rglob('*'):
    if not path.is_file() or any(part.startswith('.') for part in path.relative_to(ROOT).parts):
        continue
    if path.suffix in {'.lean', '.md', '.py', '.sh', '.toml', '.yml', '.json', '.cff'}:
        if re.search(r'[\u3400-\u9fff]', path.read_text()):
            raise SystemExit(f'Non-English prose in {path.relative_to(ROOT)}')
print(f'SOURCE_CHECK_PASS modules={len(library)} paper_checks={len(a)}')
