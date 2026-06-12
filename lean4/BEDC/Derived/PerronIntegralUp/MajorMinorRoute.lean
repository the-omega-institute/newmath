import BEDC.Derived.PerronIntegralUp.TasteGate

namespace BEDC.Derived.PerronIntegralUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PerronIntegralCarrier [AskSetup] [PackageSetup]
    (G R D M m U L E H C Q N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory G ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory M ∧
    UnaryHistory m ∧ UnaryHistory U ∧ UnaryHistory L ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory Q ∧ UnaryHistory N ∧
        Cont G R D ∧ Cont D M U ∧ Cont D m L ∧ Cont U L E ∧ Cont H C Q ∧
          PkgSig bundle Q pkg ∧ PkgSig bundle N pkg

theorem PerronIntegralMajorMinorRoute [AskSetup] [PackageSetup]
    {G R D M m U L E H C Q N upperRead lowerRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PerronIntegralCarrier G R D M m U L E H C Q N bundle pkg →
      Cont M U upperRead →
        Cont m L lowerRead →
          Cont upperRead lowerRead sealRead →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row G ∨ hsame row R ∨ hsame row D ∨ hsame row M ∨
                    hsame row m ∨ hsame row U ∨ hsame row L ∨ hsame row E ∨
                      hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont M U upperRead ∧ Cont m L lowerRead ∧
                    Cont upperRead lowerRead sealRead ∧ PkgSig bundle sealRead pkg)
                hsame ∧ UnaryHistory upperRead ∧ UnaryHistory lowerRead ∧
                  UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert UnaryHistory hsame
  intro carrier upperRoute lowerRoute sealRoute sealPkg
  obtain ⟨_GUnary, _RUnary, _DUnary, MUnary, mUnary, UUnary, LUnary, _EUnary,
    _HUnary, _CUnary, _QUnary, _NUnary, _gaugeRoute, _upperBaseRoute,
    _lowerBaseRoute, _envelopeRoute, _provenanceRoute, _provenancePkg,
    _namePkg⟩ := carrier
  have upperUnary : UnaryHistory upperRead :=
    unary_cont_closed MUnary UUnary upperRoute
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed mUnary LUnary lowerRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed upperUnary lowerUnary sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row G ∨ hsame row R ∨ hsame row D ∨ hsame row M ∨
            hsame row m ∨ hsame row U ∨ hsame row L ∨ hsame row E ∨
              hsame row sealRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont M U upperRead ∧ Cont m L lowerRead ∧
            Cont upperRead lowerRead sealRead ∧ PkgSig bundle sealRead pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, upperRoute, lowerRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, upperUnary, lowerUnary, sealUnary⟩

end BEDC.Derived.PerronIntegralUp
