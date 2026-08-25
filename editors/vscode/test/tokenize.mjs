import { readFile } from 'node:fs/promises';
import oniguruma from 'vscode-oniguruma';
import textmate from 'vscode-textmate';

const { createOnigScanner, createOnigString, loadWASM } = oniguruma;
const { Registry } = textmate;

const wasmBin = await readFile(
  new URL('../node_modules/vscode-oniguruma/release/onig.wasm', import.meta.url),
);
await loadWASM(wasmBin);

const registry = new Registry({
  onigLib: Promise.resolve({
    createOnigScanner: (sources) => createOnigScanner(sources),
    createOnigString: (str) => createOnigString(str),
  }),
  loadGrammar: async (scopeName) => {
    if (scopeName !== 'source.synquid') return null;
    const path = new URL('../syntaxes/synquid.tmLanguage.json', import.meta.url);
    return JSON.parse(await readFile(path, 'utf8'));
  },
});

const grammar = await registry.loadGrammar('source.synquid');

const fixture = `-- line comment
{- block
   comment -}
type Nat = {Int | _v >= 0}
type B = {Bool | _v == True}

data List a <p :: Int -> a -> Bool> where
  Nil :: List a <p>
  Cons :: x: {a | p 0 _v} -> xs: List a <{p (_0 + 1) _1}> -> List a <p>

termination measure len :: List a -> {Int | _v >= 0} where
  Nil -> 0
  Cons x xs -> 1 + len xs

measure elems :: List a -> Set a where
  Nil -> []
  Cons x xs -> [x] + elems xs

qualifier {x <= y, x != y, x ==> y, x + 2 <= y}

replicate :: n: Nat -> x: a -> {List a | len _v == n}
replicate = ??

caseOf = \\x . \\_ . match xs with
  Nil -> error
  Cons y ys -> Cons x ys
`;

let ruleStack = null;
const tokens = [];
for (const line of fixture.split(/\r?\n/)) {
  const { tokens: lineTokens, ruleStack: stack } = grammar.tokenizeLine(line, ruleStack);
  ruleStack = stack;
  for (const t of lineTokens) {
    tokens.push({ text: line.slice(t.startIndex, t.endIndex), scopes: t.scopes });
  }
}

let failures = 0;
function expect(name, want, inText, scopes) {
  const token = tokens.find((t) => t.text === want);
  const scoped = token && token.scopes.some((s) => scopes.some((w) => s.includes(w)));
  if (!scoped) {
    failures++;
    console.error(`FAIL ${name}: token "${want}" scopes ${token ? token.scopes : '(not found)'} missing ${scopes}`);
  } else {
    console.log(`ok   ${name}`);
  }
}

expect('line comment', '-- line comment', undefined, ['comment.line.double-dash.synquid']);
expect('block comment open', '{-', undefined, ['comment.block.synquid']);
expect('block comment close', '-}', undefined, ['comment.block.synquid']);
expect('data keyword', 'data', undefined, ['keyword.declaration.synquid']);
expect('measure keyword', 'measure ', undefined, ['keyword.declaration.synquid']);
expect('termination keyword', 'termination measure ', undefined, ['keyword.declaration.synquid']);
expect('qualifier keyword', 'qualifier', undefined, ['keyword.declaration.synquid']);
expect('type keyword', 'type', undefined, ['keyword.declaration.synquid']);
expect('where keyword', 'where', undefined, ['keyword.control.synquid']);
expect('true literal', 'True', undefined, ['constant.language.boolean.synquid']);
expect('builtin sort Int', 'Int', undefined, ['storage.type.synquid']);
expect('builtin sort Set', 'Set', undefined, ['storage.type.synquid']);
expect('constructor Nil', 'Nil', undefined, ['entity.name.type.synquid']);
expect('signature name', 'replicate', undefined, ['entity.name.function.synquid']);
expect('measure name', 'len', undefined, ['entity.name.function.synquid']);
expect('hole', '??', undefined, ['constant.placeholder.synquid']);
expect('integer', '2', undefined, ['constant.numeric.integer.synquid']);
expect('operator ==>', '==>', undefined, ['keyword.operator.synquid']);
expect('operator ::', '::', undefined, ['keyword.operator.type.synquid']);
expect('value var _v', '_v', undefined, ['variable.language.synquid']);
expect('positional var _0', '_0', undefined, ['variable.language.synquid']);
expect('wildcard _,', '_', undefined, ['variable.language.synquid']);
expect('variable xs', 'xs', undefined, ['variable.other.synquid']);

if (failures > 0) {
  console.error(`${failures} assertion(s) failed`);
  process.exit(1);
}
console.log('all assertions passed');
