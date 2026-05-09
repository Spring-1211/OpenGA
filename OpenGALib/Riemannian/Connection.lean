import OpenGALib.Riemannian.Connection.Koszul
import OpenGALib.Riemannian.Connection.LeviCivita
import OpenGALib.Riemannian.Connection.Bianchi
import OpenGALib.Riemannian.Connection.Smoothness

/-!
# Levi-Civita connection

Re-exports the Levi-Civita connection construction and its consequences:

* `Connection/Koszul.lean` — Koszul functional + algebraic identities
  (private engineering, used by the existence proof).
* `Connection/KoszulCotangent.lean` — chart-frame cotangent CLM section
  (private engineering, transitively imported via LeviCivita).
* `Connection/LeviCivita.lean` — `covDeriv` (Levi-Civita), torsion +
  metric-compatibility, locality.
* `Connection/Bianchi.lean` — `riemannCurvature` def + algebraic Bianchi I.
* `Connection/Smoothness.lean` — `covDeriv` smoothness in chart-frame
  constant directions.

Reference: do Carmo, *Riemannian Geometry*, §2 Theorem 3.6 (Levi-Civita
existence + uniqueness via Koszul); §4 Proposition 2.5 (Bianchi I).
-/
