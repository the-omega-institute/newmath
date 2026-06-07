import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BooleanalgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BooleanAlgebraCarrier [AskSetup] [PackageSetup]
    (join meet compl zero one order transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory join ∧ UnaryHistory meet ∧ UnaryHistory compl ∧ UnaryHistory zero ∧
    UnaryHistory one ∧ UnaryHistory order ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont join meet order ∧
        Cont compl zero replay ∧ Cont transport replay provenance ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem BooleanAlgebraCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {join meet compl zero one order transport replay provenance localName endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BooleanAlgebraCarrier join meet compl zero one order transport replay provenance localName
        bundle pkg →
      Cont compl zero endpoint →
        Cont endpoint one replay →
          PkgSig bundle endpoint pkg →
            SemanticNameCert
                (fun row : BHist =>
                  BooleanAlgebraCarrier join meet compl zero one order transport replay
                    provenance localName bundle pkg ∧ hsame row endpoint)
                (fun row : BHist =>
                  hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
                    hsame row one ∨ hsame row order ∨ hsame row endpoint)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle endpoint pkg)
                hsame ∧
              UnaryHistory endpoint ∧ Cont join meet order ∧ Cont compl zero endpoint ∧
                Cont endpoint one replay := by
  -- BEDC touchpoint anchor: BooleanAlgebraCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows complZero endpointOne endpointPkg
  obtain ⟨joinUnary, meetUnary, complUnary, zeroUnary, oneUnary, orderUnary,
    transportUnary, replayUnary, provenanceUnary, localNameUnary, joinMeetOrder,
    complZeroReplay, transportReplayProvenance, provenancePkg, localNamePkg⟩ :=
      carrierRows
  have carrierWitness :
      BooleanAlgebraCarrier join meet compl zero one order transport replay provenance
        localName bundle pkg := by
    exact
      ⟨joinUnary, meetUnary, complUnary, zeroUnary, oneUnary, orderUnary, transportUnary,
        replayUnary, provenanceUnary, localNameUnary, joinMeetOrder, complZeroReplay,
        transportReplayProvenance, provenancePkg, localNamePkg⟩
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed complUnary zeroUnary complZero
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            BooleanAlgebraCarrier join meet compl zero one order transport replay provenance
              localName bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
              hsame row one ∨ hsame row order ∨ hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint ⟨carrierWitness, hsame_refl endpoint⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.right)))))
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport endpointUnary (hsame_symm source.right), provenancePkg, endpointPkg⟩
  }
  exact ⟨cert, endpointUnary, joinMeetOrder, complZero, endpointOne⟩

end BEDC.Derived.BooleanalgebraUp
