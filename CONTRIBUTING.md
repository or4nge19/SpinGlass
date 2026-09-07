# Contributing

Talagrand Vol. I–II in Lean 4, Mathlib standard. Mean-field only.

Out of scope: DLR/specification theory (Georgii Ch. 1–8), 4D triviality, arithmetic models.

Lake pins are `mathlib` and [`matteo-ax/GibbsMeasure`](https://github.com/matteo-ax/GibbsMeasure)
(`lakefile.toml`). Only the exchangeability / Hewitt–Savage / de Finetti layer of the latter is
imported (`GibbsMeasure.Specification.HewittSavage`, `.DeFinetti`), through the bridge module
`SpinGlass/Limit/Exchangeability.lean`; the DLR half is not. New pins need a stated theorem that
needs them.

No `sorry`, no extra hypotheses, no duplicate APIs. Search Mathlib first.
Module `/-!`: title + objects + Vol/Thm/Eq. `/--`: one line.

`lake build SpinGlass`
