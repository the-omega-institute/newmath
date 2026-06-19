import BEDC.Derived.ReflectiveInquiryUp.LedgeredRoleCorrespondence
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ReflectiveInquiryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ReflectiveInquiryCarrier [AskSetup] [PackageSetup]
    (P F S K A R L H C Q N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory P ∧ UnaryHistory F ∧ UnaryHistory S ∧ UnaryHistory K ∧
    UnaryHistory A ∧ UnaryHistory R ∧ UnaryHistory L ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory Q ∧ UnaryHistory N ∧ Cont P F S ∧
        Cont S K A ∧ Cont R L H ∧ Cont H C Q ∧ PkgSig bundle N pkg

theorem ReflectiveInquiryCarrier_classifier_transport_certificate [AskSetup] [PackageSetup]
    {P F S K A R L H C Q N P' F' S' K' A' R' L' H' C' Q' N' bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReflectiveInquiryCarrier P F S K A R L H C Q N bundle pkg →
      ReflectiveInquiryClassifier P F S K A R L H C Q N P' F' S' K' A' R' L' H'
          C' Q' N' →
        Cont H C bridge →
          PkgSig bundle bridge pkg →
            SemanticNameCert
              (fun row : BHist => hsame row bridge ∧ UnaryHistory row)
              (fun row : BHist => hsame row bridge)
              (fun row : BHist => hsame row bridge ∧ PkgSig bundle bridge pkg)
              hsame ∧ UnaryHistory bridge := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier classifier bridgeRoute bridgePkg
  obtain ⟨_unaryP, _unaryF, _unaryS, _unaryK, _unaryA, _unaryR, _unaryL,
    unaryH, unaryC, _unaryQ, _unaryN, _routePF, _routeSK, _routeRL, _routeHC,
    _pkgN⟩ := carrier
  obtain ⟨_sameP, _sameF, _sameS, _sameK, _sameA, _sameR, _sameL, _sameH,
    _sameC, _sameQ, _sameN⟩ := classifier
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed unaryH unaryC bridgeRoute
  have sourceBridge :
      (fun row : BHist => hsame row bridge ∧ UnaryHistory row) bridge := by
    exact ⟨hsame_refl bridge, bridgeUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row bridge ∧ UnaryHistory row)
        (fun row : BHist => hsame row bridge)
        (fun row : BHist => hsame row bridge ∧ PkgSig bundle bridge pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro bridge sourceBridge
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, bridgePkg⟩
  }
  exact ⟨cert, bridgeUnary⟩

end BEDC.Derived.ReflectiveInquiryUp
