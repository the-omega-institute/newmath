import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.LocatedCompactUp.TasteGate

namespace BEDC.Derived.LocatedCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedCompactCarrier [AskSetup] [PackageSetup]
    (X L F A H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist BMark
  UnaryHistory X ∧ UnaryHistory L ∧ UnaryHistory F ∧ UnaryHistory A ∧ Cont L F C ∧
    hsame H (append X A) ∧ PkgSig bundle P pkg ∧ hsame N (append C P)

theorem LocatedCompactCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X L F A H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCompactCarrier X L F A H C P N bundle pkg ->
      SemanticNameCert
        (fun row : BHist => LocatedCompactCarrier X L F A H C P N bundle pkg /\ hsame row N)
        (fun row : BHist => LocatedCompactCarrier X L F A H C P N bundle pkg /\ hsame row N)
        (fun row : BHist => LocatedCompactCarrier X L F A H C P N bundle pkg /\ hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist BMark
  intro carrier
  constructor
  · constructor
    · exact Exists.intro N (And.intro carrier (hsame_refl N))
    · intro row _source
      exact hsame_refl row
    · intro row row' same
      exact hsame_symm same
    · intro row row' row'' sameRow sameRow'
      exact hsame_trans sameRow sameRow'
    · intro row row' sameRows sourceRow
      exact And.intro carrier (hsame_trans (hsame_symm sameRows) sourceRow.right)
  · intro _row source
    exact source
  · intro _row source
    exact source

end BEDC.Derived.LocatedCompactUp
