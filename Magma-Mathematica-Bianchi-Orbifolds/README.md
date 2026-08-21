# Bianchi orbifolds

Computations of fundamental domains for arithmetic Kleinian groups, and the
resulting data for Bianchi orbifolds. Magma does the domain computation; the
Mathematica notebooks drive it, check the results, and analyse the output.

## My own work

Top level:

- `JK-Bianchi-rev7.nb`, `JK-Bianchi-rev7-test-d-19.nb` — main notebooks driving
  the computation and inspecting the output.
- `JK-Bianchi-FD-rev5.m` — Magma driver script.
- `221213-equivalence-check.nb`, `221213-equivalence-check-pdf.pdf` — equivalence
  checks on the computed domains.
- `ECTGS.nb`, `IsomSphere.nb` — supporting notebooks.
- `matrixN.m`, `volume_formula.m`, `magma-simple-data.m` — supporting Magma code.
- `JK-Bianchi-FD-*.txt` — computed output: generators, faces, edges, PSL matrices,
  quotients, and H1/pi1 generators.
- `FinalFDom.mpl`, `FinalFDomS.mpl`, `FinalFDomC.mpl` — Maple code plotting the
  computed fundamental domain. These are output, not source: the package writes
  them on a run with `Maple := true`, so each copy below carries its own set from
  whichever computation was run there.

In `magma-bianchi2021/`:

- `bianchi-JK2021.m` — the 2021 Magma driver, the largest piece of my code here.
- Two `.webloc` bookmarks into the Magma handbook.

## Third-party: KleinianGroups (GPL v3)

Everything else is **KleinianGroups 1.0** (September 25, 2012) by **Aurel Page**,
a Magma package computing fundamental domains for arithmetic Kleinian groups.
It is redistributed under the **GNU General Public License v3** — see `COPYING`
for the license and `README.txt` for the package's own documentation.

The package files are `klngpspec`, `kleinian.m`, `aux.m`, `bianchi.m`,
`example.m`, and the `geometry/`, `fundamentaldomains/`, and `drawing/`
directories, together with their `.sig` files, `changelog`, `README.txt`, and
`COPYING`.

Three copies are present, kept because different computations were run against
different ones:

| Location | What it is |
|---|---|
| this directory | the package, unmodified, alongside my run output |
| `magma-bianchi2021/KleinianGroups-1.0/` | the package, unmodified |
| `magma-bianchi2021/KleinianGroups-1.0.zip` | the original distribution archive |
| `magma-bianchi2021/KG-win/` | **modified** — see below |

### Changes made to KG-win

`KG-win` is a modified copy of KleinianGroups 1.0. The only change is that
`aux.m` is renamed to `aux2.m`, with `klngpspec` and every `import` statement
updated to match, because `aux` is a reserved device name on Windows and the
file cannot be created there. No functional code was altered.

This notice is given as required by section 5 of the GPL v3.
