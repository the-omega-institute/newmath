import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalRootNamecertAcceptance [AskSetup] [PackageSetup]
    {cantor fan tolerance branch depth witness modulus transport replay provenance localName
      acceptedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus transport replay
        provenance localName bundle pkg →
      Cont transport localName acceptedRead →
        PkgSig bundle acceptedRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row acceptedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row cantor ∨ hsame row fan ∨ hsame row tolerance ∨
                  hsame row branch ∨ hsame row depth ∨ hsame row witness ∨
                    hsame row modulus ∨ hsame row acceptedRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont transport localName acceptedRead ∧
                  PkgSig bundle acceptedRead pkg)
              hsame ∧ UnaryHistory acceptedRead := by
  -- BEDC touchpoint anchor: FanFunctionalCarrierSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier transportLocalAccepted acceptedPkg
  obtain ⟨_cantorUnary, _fanUnary, _toleranceUnary, _branchUnary, _depthUnary,
    _witnessUnary, _modulusUnary, transportUnary, _replayUnary, _provenanceUnary,
    localNameUnary, _transportLocalName, _branchDepthWitness, _witnessModulusReplay,
    _provenancePkg⟩ := carrier
  have acceptedUnary : UnaryHistory acceptedRead :=
    unary_cont_closed transportUnary localNameUnary transportLocalAccepted
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row acceptedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cantor ∨ hsame row fan ∨ hsame row tolerance ∨
              hsame row branch ∨ hsame row depth ∨ hsame row witness ∨
                hsame row modulus ∨ hsame row acceptedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont transport localName acceptedRead ∧
              PkgSig bundle acceptedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro acceptedRead ⟨hsame_refl acceptedRead, acceptedUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, transportLocalAccepted, acceptedPkg⟩
  }
  exact ⟨cert, acceptedUnary⟩

end BEDC.Derived.FanfunctionalUp
