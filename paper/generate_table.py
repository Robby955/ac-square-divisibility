"""Render the paper's exact macro table from the frozen affine entry route."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def exponent(coeffs):
    # Put variable terms first; this changes notation only.
    parts = []
    for coefficient, name in ((coeffs[1], "p"), (coeffs[2], "s"), (coeffs[0], "")):
        if coefficient:
            term = ("" if abs(coefficient) == 1 and name else str(abs(coefficient))) + name
            parts.append(("-" if coefficient < 0 else "+") + term)
    return "".join(parts).lstrip("+") or "0"


def word(blocks):
    result = ""
    for generator, coefficients in blocks:
        exp = exponent(coefficients)
        if exp != "0":
            result += generator if exp == "1" else generator + "^{" + exp + "}"
    return result or "1"


def main():
    route = json.loads((HERE.parent / "entry_route.json").read_text())["route"]
    lines = [r"\begin{longtable}{r@{\qquad}l}", r"\toprule",
             r"Row & Operation\\\midrule\endhead"]
    for number, (kind, slot, *args) in enumerate(route, 1):
        if kind == "conj":
            operation = f"C_{{{slot}}}({word(args[0])})"
        elif kind == "mul":
            operation = f"M_{{{slot}}}^{{{args[0]}}}"
        else:
            operation = f"I_{{{slot}}}"
        lines.append(f"{number} & ${operation}$" + r"\\")
    lines.extend([r"\bottomrule", r"\end{longtable}"])
    (HERE / "entry-table.tex").write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
