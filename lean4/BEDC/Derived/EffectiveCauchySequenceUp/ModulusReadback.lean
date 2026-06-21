import BEDC.Derived.EffectiveCauchySequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EffectiveCauchySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EffectiveCauchySequenceModulusReadback [AskSetup] [PackageSetup]
    {S M W D Q E H C P N modulusRead windowRead dyadicRead readbackRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S ->
      UnaryHistory M ->
        UnaryHistory W ->
          UnaryHistory D ->
            UnaryHistory Q ->
              UnaryHistory E ->
                Cont S M modulusRead ->
                  Cont modulusRead W windowRead ->
                    Cont windowRead D dyadicRead ->
                      Cont dyadicRead Q readbackRead ->
                        Cont readbackRead E sealRead ->
                          PkgSig bundle N pkg ->
                            (exists packet : EffectiveCauchySequenceUp,
                              packet = EffectiveCauchySequenceUp.mk S M W D Q E H C P N) ∧
                              SemanticNameCert
                                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row S ∨ hsame row M ∨ hsame row W ∨
                                    hsame row D ∨ hsame row Q ∨ hsame row E ∨
                                      hsame row sealRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont S M modulusRead ∧
                                    Cont modulusRead W windowRead ∧
                                      Cont windowRead D dyadicRead ∧
                                        Cont dyadicRead Q readbackRead ∧
                                          Cont readbackRead E sealRead ∧
                                            PkgSig bundle N pkg)
                                hsame ∧
                                UnaryHistory modulusRead ∧ UnaryHistory windowRead ∧
                                  UnaryHistory dyadicRead ∧ UnaryHistory readbackRead ∧
                                    UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro sUnary mUnary wUnary dUnary qUnary eUnary modulusRoute windowRoute dyadicRoute
    readbackRoute sealRoute namePkg
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed sUnary mUnary modulusRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed modulusUnary wUnary windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary dUnary dyadicRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed dyadicUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row S ∨ hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row Q ∨
            hsame row E ∨ hsame row sealRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont S M modulusRead ∧ Cont modulusRead W windowRead ∧
            Cont windowRead D dyadicRead ∧ Cont dyadicRead Q readbackRead ∧
              Cont readbackRead E sealRead ∧ PkgSig bundle N pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, modulusRoute, windowRoute, dyadicRoute, readbackRoute, sealRoute,
          namePkg⟩
  }
  exact
    ⟨Exists.intro (EffectiveCauchySequenceUp.mk S M W D Q E H C P N) rfl, cert,
      modulusUnary, windowUnary, dyadicUnary, readbackUnary, sealUnary⟩

end BEDC.Derived.EffectiveCauchySequenceUp
