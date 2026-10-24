// Use the installed KaTeX bundle strictly as a local TeX-to-MathML parser.
// No browser, network resources, or HTML execution is required.
const fs = require('fs');
const vm = require('vm');
const bundle = process.env.KATEX_BUNDLE || '/Applications/Visual Studio Code.app/Contents/Resources/app/extensions/markdown-math/notebook-out/katex.js';
let code = fs.readFileSync(bundle, 'utf8')
  .replace(/export\{[^}]+\};?\s*$/, '')
  .replaceAll('import.meta.url', '"file:///katex.js"');
const context = {};
vm.createContext(context);
vm.runInContext(code, context);
const katex = vm.runInContext('rn()', context);
const file = process.argv[2];
const data = JSON.parse(fs.readFileSync(file, 'utf8'));
const math = (tex, display) => {
  const html = katex.renderToString(tex, {output: 'mathml', displayMode: display, throwOnError: true, strict: 'error'});
  const found = html.match(/<math[\s\S]*<\/math>/);
  if (!found) throw new Error('Missing MathML: ' + tex);
  return found[0];
};
let formulas = 0;
for (const block of data.blocks) {
  if (block.kind === 'equation') {
    block.mathml = math(block.text, true);
    formulas++;
  } else {
    block.runs = block.text.split(/(\$[^$]+\$)/g).filter(Boolean).map(part => {
      if (part.startsWith('$') && part.endsWith('$')) {
        formulas++;
        return {text: part.slice(1,-1), mathml: math(part.slice(1,-1), false)};
      }
      return {text: part};
    });
  }
}
data.katexVersion = katex.version;
data.formulas = formulas;
fs.writeFileSync(file, JSON.stringify(data, null, 2));
console.log(`Parsed ${formulas} formulas with KaTeX ${katex.version}.`);
