import BEDC.Derived.LongLineUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LongLineUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LongLineCarrier [AskSetup] [PackageSetup]
    (S I O T H C P N compareRead topologyRead nameRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory S ∧ UnaryHistory I ∧ UnaryHistory O ∧ UnaryHistory T ∧
    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      Cont S I compareRead ∧ Cont compareRead O topologyRead ∧
        Cont H C nameRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem LongLineCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S I O T H C P N compareRead topologyRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LongLineCarrier S I O T H C P N compareRead topologyRead nameRead bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row S ∨ hsame row I ∨ hsame row O ∨ hsame row T ∨ hsame row H ∨
            hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row compareRead ∨
              hsame row topologyRead ∨ hsame row nameRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont S I compareRead ∧ Cont compareRead O topologyRead ∧
            Cont H C nameRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame ∧ UnaryHistory compareRead ∧ UnaryHistory topologyRead ∧
          UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨unaryS, unaryI, unaryO, _unaryT, unaryH, unaryC, _unaryP, _unaryN,
    compareRoute, topologyRoute, nameRoute, provenancePkg, namePkg⟩ := carrier
  have compareUnary : UnaryHistory compareRead := unary_cont_closed unaryS unaryI compareRoute
  have topologyUnary : UnaryHistory topologyRead :=
    unary_cont_closed compareUnary unaryO topologyRoute
  have nameUnary : UnaryHistory nameRead := unary_cont_closed unaryH unaryC nameRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row S ∨ hsame row I ∨ hsame row O ∨ hsame row T ∨ hsame row H ∨
            hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row compareRead ∨
              hsame row topologyRead ∨ hsame row nameRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont S I compareRead ∧ Cont compareRead O topologyRead ∧
            Cont H C nameRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRead ⟨hsame_refl nameRead, nameUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compareRoute, topologyRoute, nameRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, compareUnary, topologyUnary, nameUnary⟩

end BEDC.Derived.LongLineUp
