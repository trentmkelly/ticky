// Syntax highlighting for Ticky: Python's syntax plus a few words of its own.
import { StreamLanguage, StringStream } from "@codemirror/language";

const keywords = new Set([
  "if", "elif", "else", "while", "for", "in", "break", "continue", "pass", "def", "return", "and", "or",
  "not", "is", "global", "assert", "import", "from", "nonlocal", "del", "lambda",
  // Ticky's own
  "every", "tick", "ticks", "wait", "until", "input", "output", "test", "set", "run", "process", "max",
]);
const atoms = new Set(["True", "False", "None"]);
const builtins = new Set([
  "len", "min", "abs", "range", "sum", "S", "Bundle", "Signal", "port", "int", "bool", "print",
  "controls", "display", "items", "quality", "random", "speaker", "enumerate", "zip", "sorted",
]);

interface State {
  // Inside a triple-quoted string (its quote), or null.
  triple: string | null;
}

export const ticky = StreamLanguage.define<State>({
  name: "ticky",
  startState: () => ({ triple: null }),
  token(stream: StringStream, state: State) {
    if (state.triple) {
      while (!stream.eol()) {
        if (stream.match(state.triple)) {
          state.triple = null;
          return "string";
        }
        stream.next();
      }
      return "string";
    }
    if (stream.eatSpace()) return null;
    if (stream.match("#")) {
      stream.skipToEnd();
      return "comment";
    }
    const triple = stream.match(/^("""|''')/);
    if (triple) {
      state.triple = (triple as RegExpMatchArray)[0];
      return "string";
    }
    if (stream.match(/^"([^"\\]|\\.)*"?/) || stream.match(/^'([^'\\]|\\.)*'?/)) return "string";
    if (stream.match(/^0[xX][0-9a-fA-F_]+/) || stream.match(/^0[bB][01_]+/) || stream.match(/^\d[\d_]*/)) return "number";
    // `@ X`: the signal a port is on.
    if (stream.match(/^@\s*[A-Za-z][\w-]*/)) return "meta";
    const word = stream.match(/^[A-Za-z_]\w*/);
    if (word) {
      const w = (word as RegExpMatchArray)[0];
      if (keywords.has(w)) return "keyword";
      if (atoms.has(w)) return "atom";
      if (builtins.has(w)) return "builtin";
      if (stream.match(/^\s*\(/, false)) return "variableName.function";
      return "variableName";
    }
    if (stream.match(/^(\*\*|\/\/|<<|>>|[<>=!]=|[-+*/%&|^~<>=])/)) return "operator";
    stream.next();
    return "punctuation";
  },
  languageData: { commentTokens: { line: "#" }, indentOnInput: /^\s*(else|elif)\b/ },
});
