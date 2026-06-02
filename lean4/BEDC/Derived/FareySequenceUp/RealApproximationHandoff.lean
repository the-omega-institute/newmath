import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceRealApproximationHandoff [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N rationalRead windowRead regularRead
      approximationRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont D Q rationalRead ->
        Cont rationalRead W windowRead ->
          Cont windowRead R regularRead ->
            Cont regularRead G approximationRead ->
              Cont approximationRead E sealRead ->
                PkgSig bundle sealRead pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row D ∨ hsame row Q ∨ hsame row W ∨ hsame row R ∨
                        hsame row G ∨ hsame row E ∨ hsame row rationalRead ∨
                          hsame row windowRead ∨ hsame row regularRead ∨
                            hsame row approximationRead ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont D Q rationalRead ∧
                        Cont rationalRead W windowRead ∧ Cont windowRead R regularRead ∧
                          Cont regularRead G approximationRead ∧
                            Cont approximationRead E sealRead ∧ PkgSig bundle sealRead pkg)
                    hsame ∧
                    UnaryHistory rationalRead ∧ UnaryHistory windowRead ∧
                      UnaryHistory regularRead ∧ UnaryHistory approximationRead ∧
                        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier rationalRoute windowRoute regularRoute approximationRoute sealRoute sealPkg
  obtain ⟨_unaryB, _unaryA, _unaryM, _unaryL, _unaryT, _unaryS, unaryD, unaryQ,
    unaryW, unaryR, unaryG, unaryE, _unaryH, _unaryC, _unaryP, _unaryN, _emptyA,
    _emptyS, _emptyM, _emptyG, _emptyE, _carrierPkg⟩ := carrier
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed unaryD unaryQ rationalRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed rationalUnary unaryW windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary unaryR regularRoute
  have approximationUnary : UnaryHistory approximationRead :=
    unary_cont_closed regularUnary unaryG approximationRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed approximationUnary unaryE sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row Q ∨ hsame row W ∨ hsame row R ∨ hsame row G ∨
              hsame row E ∨ hsame row rationalRead ∨ hsame row windowRead ∨
                hsame row regularRead ∨ hsame row approximationRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D Q rationalRead ∧
              Cont rationalRead W windowRead ∧ Cont windowRead R regularRead ∧
                Cont regularRead G approximationRead ∧ Cont approximationRead E sealRead ∧
                  PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
        ⟨source.right, rationalRoute, windowRoute, regularRoute, approximationRoute,
          sealRoute, sealPkg⟩
  }
  exact ⟨cert, rationalUnary, windowUnary, regularUnary, approximationUnary, sealUnary⟩

end BEDC.Derived.FareySequenceUp
