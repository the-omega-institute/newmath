import BEDC.Derived.RegularCauchyMinUp.CarrierAdmission
import BEDC.FKernel.Package

namespace BEDC.Derived.RegularCauchyMinUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyMinCarrier_apartness_stability [AskSetup] [PackageSetup]
    {A B W DA DB J S R E H C P N leftRead rightRead apartnessRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyMinCarrier A B W DA DB J S R E H C P N →
      Cont A W leftRead →
        Cont B W rightRead →
          Cont leftRead J apartnessRead →
            Cont apartnessRead E publicRead →
              PkgSig bundle P pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
                        hsame row DB ∨ hsame row J ∨ hsame row S ∨ hsame row R ∨
                          hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                            hsame row N ∨ hsame row leftRead ∨ hsame row rightRead ∨
                              hsame row apartnessRead ∨ hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧
                        RegularCauchyMinCarrier A B W DA DB J S R E H C P N ∧
                          Cont A W leftRead ∧ Cont B W rightRead ∧
                            Cont leftRead J apartnessRead ∧
                              Cont apartnessRead E publicRead ∧ PkgSig bundle P pkg)
                    hsame ∧
                  UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                    UnaryHistory apartnessRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: RegularCauchyMinCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier leftRoute rightRoute apartnessRoute publicRoute publicPkg
  have carrierWitness : RegularCauchyMinCarrier A B W DA DB J S R E H C P N :=
    carrier
  obtain ⟨aUnary, bUnary, wUnary, _daUnary, _dbUnary, jUnary, _sUnary, _rUnary,
    eUnary, _hUnary, _cUnary, _pUnary, _nUnary⟩ := carrier
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed aUnary wUnary leftRoute
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed bUnary wUnary rightRoute
  have apartnessUnary : UnaryHistory apartnessRead :=
    unary_cont_closed leftUnary jUnary apartnessRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed apartnessUnary eUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
              hsame row DB ∨ hsame row J ∨ hsame row S ∨ hsame row R ∨
                hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row N ∨ hsame row leftRead ∨ hsame row rightRead ∨
                    hsame row apartnessRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              RegularCauchyMinCarrier A B W DA DB J S R E H C P N ∧
                Cont A W leftRead ∧ Cont B W rightRead ∧
                  Cont leftRead J apartnessRead ∧ Cont apartnessRead E publicRead ∧
                    PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, carrierWitness, leftRoute, rightRoute, apartnessRoute, publicRoute,
          publicPkg⟩
  }
  exact ⟨cert, leftUnary, rightUnary, apartnessUnary, publicUnary⟩

end BEDC.Derived.RegularCauchyMinUp
