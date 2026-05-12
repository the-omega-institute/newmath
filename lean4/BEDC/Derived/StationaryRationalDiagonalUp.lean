import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StationaryRationalDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StationaryRationalDiagonalCarrier [AskSetup] [PackageSetup]
    (q stream regular diagonal realSeal transports routes provenance namecert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory q ∧ UnaryHistory stream ∧ UnaryHistory regular ∧ UnaryHistory diagonal ∧
    UnaryHistory realSeal ∧ UnaryHistory transports ∧ UnaryHistory routes ∧
      UnaryHistory provenance ∧ UnaryHistory namecert ∧ Cont q stream regular ∧
        Cont regular diagonal realSeal ∧ Cont transports routes namecert ∧
          PkgSig bundle provenance pkg

theorem StationaryRationalDiagonalCarrier_namecert_obligation_surface [AskSetup]
    [PackageSetup]
    {q stream regular diagonal realSeal transports routes provenance namecert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StationaryRationalDiagonalCarrier q stream regular diagonal realSeal transports routes
        provenance namecert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          StationaryRationalDiagonalCarrier q stream regular diagonal realSeal transports routes
            provenance namecert bundle pkg ∧ hsame row realSeal)
        (fun row : BHist =>
          StationaryRationalDiagonalCarrier q stream regular diagonal realSeal transports routes
            provenance namecert bundle pkg ∧ hsame row realSeal)
        (fun row : BHist =>
          StationaryRationalDiagonalCarrier q stream regular diagonal realSeal transports routes
            provenance namecert bundle pkg ∧ hsame row realSeal)
        hsame := by
  intro carrier
  refine {
    core := ?_
    pattern_sound := ?_
    ledger_sound := ?_
  }
  · exact {
      carrier_inhabited := Exists.intro realSeal ⟨carrier, hsame_refl realSeal⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
  · intro _row source
    exact source
  · intro _row source
    exact source

end BEDC.Derived.StationaryRationalDiagonalUp
