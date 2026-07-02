import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive RegularCauchyDensityUp : Type where
  | mk (Q S R A E H C P N : BHist) : RegularCauchyDensityUp
  deriving DecidableEq

namespace RegularCauchyDensityUp

def fields : RegularCauchyDensityUp → List BHist
  | RegularCauchyDensityUp.mk Q S R A E H C P N => [Q, S, R, A, E, H, C, P, N]

theorem field_count (x : RegularCauchyDensityUp) : (fields x).length = 9 := by
  cases x
  rfl

end RegularCauchyDensityUp

def RegularCauchyDensityCarrier [AskSetup] [PackageSetup]
    (Q S R A E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig UnaryHistory
  UnaryHistory Q ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory A ∧
    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ PkgSig bundle E pkg

theorem RegularCauchyDensityRegSeqRatHandoff [AskSetup] [PackageSetup]
    {Q S R A E H C P N windowRead readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDensityCarrier Q S R A E H C P N bundle pkg ->
      Cont S R windowRead ->
        Cont windowRead A readbackRead ->
          Cont readbackRead E sealRead ->
            PkgSig bundle sealRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row A ∨
                      hsame row E ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont S R windowRead ∧
                      Cont windowRead A readbackRead ∧ Cont readbackRead E sealRead ∧
                        PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                  UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier windowRoute readbackRoute sealRoute sealPkg
  obtain ⟨_qUnary, sUnary, rUnary, aUnary, eUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _carrierPkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sUnary rUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary aUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row A ∨
              hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R windowRead ∧
              Cont windowRead A readbackRead ∧ Cont readbackRead E sealRead ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead
        ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRoute, readbackRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, windowUnary, readbackUnary, sealUnary⟩

end BEDC.Derived
