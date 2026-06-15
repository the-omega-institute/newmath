import BEDC.Derived.HyperbolicHoroballShadowUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HyperbolicHoroballShadowUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperbolicHoroballShadowNamecertObligations [AskSetup] [PackageSetup]
    {B V M O S R E H C P N shadowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B -> UnaryHistory V -> UnaryHistory M -> UnaryHistory O ->
      UnaryHistory S -> UnaryHistory R -> UnaryHistory E -> Cont B V shadowRead ->
        Cont shadowRead E sealRead -> PkgSig bundle P pkg -> PkgSig bundle N pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row B ∨ hsame row V ∨ hsame row M ∨ hsame row O ∨
                  hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row sealRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory shadowRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro bUnary vUnary _mUnary _oUnary _sUnary _rUnary eUnary shadowRoute sealRoute
    provenancePkg namePkg
  have shadowUnary : UnaryHistory shadowRead :=
    unary_cont_closed bUnary vUnary shadowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed shadowUnary eUnary sealRoute
  have sourceAtSeal : hsame sealRead sealRead ∧ UnaryHistory sealRead :=
    ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row V ∨ hsame row M ∨ hsame row O ∨
              hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceAtSeal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact ⟨cert, shadowUnary, sealUnary⟩

end BEDC.Derived.HyperbolicHoroballShadowUp
