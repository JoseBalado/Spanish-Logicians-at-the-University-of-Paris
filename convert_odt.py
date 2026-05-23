#!/usr/bin/env python3
"""
Convert ODT source files to Markdown with Jekyll front matter.

Usage:
    python3 convert_odt.py

Add new entries to FILES below when a new ODT is added to a philosopher folder.
The 'src' path is relative to philosophers/, the 'dst' is where the .md is written
(also relative to philosophers/).  Images are extracted into a Pictures/ subfolder
next to the output file.

Naming convention for dst:
  - Resolve abbreviated letters in square brackets: Dialectice[n] → Dialecticen
  - Strip library signatures and (Place Year) from filename
  - Use hyphens, no spaces
  - If two editions exist of the same work, append the year: ...-1521.md / ...-1527.md
  - Fix obvious spelling errors in the original title (e.g. Summule → Summulae)
"""

import subprocess
import os

# Root of the philosophers directory
PHIL = os.path.join(os.path.dirname(os.path.abspath(__file__)), "philosophers")


FILES = [
    # ── Gaspar Lax ────────────────────────────────────────────────────────────
    {
        "src": "Gaspar-Lax/Tractatus summularum [Dh38](Cesaraugustane 1521).odt",
        "dst": "Gaspar-Lax/Tractatus-Summularum.md",
        "title": "Tractatus Summularum",
        "author": "Gaspar Lax",
        "year": 1521,
        "place": "Caesaraugustae (Zaragoza)",
        "signature": "Dh38",
        "library": "R. Biblioteca Universitaria Alessandrina, Roma",
        "description": (
            "Tractatus Summularum by Gaspar Lax, Zaragoza 1521. "
            "A manual of logic in the summulae tradition by the 'Prince of Sophists' "
            "of the Collège de Montaigu, Paris."
        ),
        "keywords": (
            "Gaspar Lax, Tractatus Summularum, logic, summulae, "
            "University of Paris, Collège de Montaigu, medieval logic, "
            "renaissance logic, Zaragoza 1521"
        ),
    },
    # ── John Mair ─────────────────────────────────────────────────────────────
    {
        "src": "John-Mair/Introdvctorium in Aristotelica[m] Dialecticen, tota[m]q[ue] Logice[n] [999%Philos.2276](Paris 1521).odt",
        "dst": "John-Mair/Introdvctorium-in-Aristotelicam-Dialecticen-1521.md",
        "title": "Introdvctorium in Aristotelicam Dialecticen (Paris 1521)",
        "author": "John Mair",
        "year": 1521,
        "place": "Paris",
        "signature": "999%Philos.2276",
        "library": "",
        "description": (
            "Introdvctorium in Aristotelicam Dialecticen by John Mair, Paris 1521. "
            "An introduction to Aristotelian dialectic covering the whole of logic."
        ),
        "keywords": (
            "John Mair, John Major, Introdvctorium, Aristotelian dialectic, "
            "logic, University of Paris, medieval logic, renaissance logic, Paris 1521"
        ),
    },
    {
        "src": "John-Mair/Introductorium perutile in Aristotelicum dialecticen [2 Ph.sp. 23 s](S.l. 1527).odt",
        "dst": "John-Mair/Introductorium-perutile-in-Aristotelicum-dialecticen-1527.md",
        "title": "Introductorium perutile in Aristotelicum dialecticen (1527)",
        "author": "John Mair",
        "year": 1527,
        "place": "S.l.",
        "signature": "2 Ph.sp. 23 s",
        "library": "",
        "description": (
            "Introductorium perutile in Aristotelicum dialecticen by John Mair, 1527. "
            "A concise introduction to Aristotelian dialectic."
        ),
        "keywords": (
            "John Mair, John Major, Introductorium perutile, Aristotelian dialectic, "
            "logic, University of Paris, medieval logic, renaissance logic, 1527"
        ),
    },
    # ── Jerónimo Pardo ────────────────────────────────────────────────────────
    {
        "src": "Jeronimo-Pardo/Medulla_Dyallectices.odt",
        "dst": "Jeronimo-Pardo/Medulla-Dyalectices.md",
        "title": "Medulla Dyalectices",
        "author": "Jerónimo Pardo",
        "year": 1505,
        "place": "Paris",
        "signature": "2 Ph.sp. 35",
        "library": "Bayerische Staatsbibliothek, München",
        "description": (
            "Medulla Dyalectices by Jerónimo Pardo, posthumous edition Paris 1505, "
            "edited by John Mair and Jacobo Ortiz. "
            "A comprehensive manual of logic covering consequences, modals, "
            "syllogistics, and the descensus."
        ),
        "keywords": (
            "Jerónimo Pardo, Medulla Dyalectices, logic, consequences, modals, "
            "syllogistics, descensus, University of Paris, Collège de Montaigu, "
            "medieval logic, renaissance logic, John Mair, Jacobo Ortiz"
        ),
    },
    # ── Domingo de Soto ───────────────────────────────────────────────────────
    {
        "src": "Domingo-de-Soto/Summule [21393](Burgis 1529).odt",
        "dst": "Domingo-de-Soto/Summulae.md",
        "title": "Summulae",
        "author": "Domingo de Soto",
        "year": 1529,
        "place": "Burgis (Burgos)",
        "signature": "21393",
        "library": "",
        "description": (
            "Summulae by Domingo de Soto, Burgos 1529. "
            "A manual of logic in the summulae tradition, written after his "
            "Paris formation under Juan de Celaya at the Collège Sainte-Barbe."
        ),
        "keywords": (
            "Domingo de Soto, Summulae, logic, Burgos 1529, Dominican, "
            "medieval logic, renaissance logic, School of Salamanca, "
            "Juan de Celaya, University of Paris"
        ),
    },
    # ── Fernando de Enzinas ───────────────────────────────────────────────────
    {
        "src": "Fernando-de-Enzinas/Tractatus de côpositione propositionis mentalis [a-004-392 (3)](Lugduni 1528).odt",
        "dst": "Fernando-de-Enzinas/Tractatus-de-compositione-propositionis-mentalis.md",
        "title": "Tractatus de compositione propositionis mentalis",
        "author": "Fernando de Enzinas",
        "year": 1528,
        "place": "Lugduni (Lyon)",
        "signature": "a-004-392 (3)",
        "library": "",
        "description": (
            "Tractatus de compositione propositionis mentalis by Fernando de Enzinas, Lyon 1528. "
            "A treatise on the composition of mental propositions and the nature of "
            "syncategorematic acts, revised by Robert Wauchop."
        ),
        "keywords": (
            "Fernando de Enzinas, Tractatus de compositione propositionis mentalis, "
            "mental proposition, syncategoremata, logic, Lyon 1528, "
            "University of Paris, medieval logic, renaissance logic, Robert Wauchop"
        ),
    },
]


def build_front_matter(f):
    lines = ["---", "layout: source"]
    lines.append(f'title: "{f["title"]}"')
    lines.append(f'author: "{f["author"]}"')
    lines.append(f'year: {f["year"]}')
    lines.append(f'place: "{f["place"]}"')
    if f.get("signature"):
        lines.append(f'signature: "{f["signature"]}"')
    if f.get("library"):
        lines.append(f'library: "{f["library"]}"')
    lines.append("description: >-")
    lines.append(f'  {f["description"]}')
    lines.append("keywords: >-")
    lines.append(f'  {f["keywords"]}')
    lines.append("---")
    lines.append("")
    return "\n".join(lines)


def convert(f):
    src = os.path.join(PHIL, f["src"])
    dst = os.path.join(PHIL, f["dst"])
    dst_dir = os.path.dirname(dst)

    if not os.path.exists(src):
        print(f"  SKIP (source not found): {f['src']}")
        return False

    if os.path.exists(dst):
        print(f"  SKIP (already exists): {f['dst']}")
        return False

    cmd = [
        "pandoc",
        "-f", "odt",
        "-t", "markdown",
        "--wrap=none",
        "--extract-media=.",   # images extracted relative to dst_dir
        os.path.abspath(src),
    ]
    result = subprocess.run(cmd, capture_output=True, text=True, cwd=dst_dir)

    if result.returncode != 0:
        print(f"  ERROR: {result.stderr.strip()}")
        return False

    with open(dst, "w", encoding="utf-8") as fh:
        fh.write(build_front_matter(f))
        fh.write("\n")
        fh.write(result.stdout)

    return True


def main():
    for f in FILES:
        print(f"Converting -> {f['dst']} ... ", end="", flush=True)
        ok = convert(f)
        if ok:
            print("OK")


if __name__ == "__main__":
    main()
