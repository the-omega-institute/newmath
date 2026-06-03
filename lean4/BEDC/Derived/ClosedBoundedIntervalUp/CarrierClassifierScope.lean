import BEDC.Derived.ClosedBoundedIntervalUp.Classifier

namespace BEDC.Derived.ClosedBoundedIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_carrier_classifier_scope [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported lower2 upper2 order2 rational2 dyadic2 stream2 readback2 sealRow2
      transport2 replay2 provenance2 localName2 exported2 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalClassifier lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported lower2 upper2 order2 rational2 dyadic2
        stream2 readback2 sealRow2 transport2 replay2 provenance2 localName2 exported2 bundle
        pkg →
      SemanticNameCert
          (fun row : BHist => (hsame row localName ∨ hsame row localName2) ∧
            UnaryHistory row)
          (fun row : BHist =>
            hsame row lower ∨ hsame row upper ∨ hsame row order ∨ hsame row dyadic ∨
              hsame row stream ∨ hsame row readback ∨ hsame row sealRow ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row localName ∨ hsame row localName2)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame ∧
        hsame lower lower2 ∧ hsame upper upper2 ∧ hsame order order2 := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro classified
  obtain ⟨packet, packet2, sameLower, sameUpper, sameOrder, _sameRational, _sameDyadic,
    _sameStream, _sameReadback, _sameSealRow⟩ := classified
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, _dyadicUnary,
    _streamUnary, _readbackUnary, _sealRowUnary, _transportUnary, _replayUnary,
    _provenanceUnary, localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute,
    _sealRoute, _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  obtain ⟨_lowerUnary2, _upperUnary2, _orderUnary2, _rationalUnary2, _dyadicUnary2,
    _streamUnary2, _readbackUnary2, _sealRowUnary2, _transportUnary2, _replayUnary2,
    _provenanceUnary2, localNameUnary2, _exportedUnary2, _endpointRoute2,
    _containmentRoute2, _sealRoute2, _replayRoute2, _nameRoute2, _provenancePkg2,
    _localNamePkg2⟩ := packet2
  have cert :
      SemanticNameCert
          (fun row : BHist => (hsame row localName ∨ hsame row localName2) ∧
            UnaryHistory row)
          (fun row : BHist =>
            hsame row lower ∨ hsame row upper ∨ hsame row order ∨ hsame row dyadic ∨
              hsame row stream ∨ hsame row readback ∨ hsame row sealRow ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row localName ∨ hsame row localName2)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro localName ⟨Or.inl (hsame_refl localName), localNameUnary⟩
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
        constructor
        · cases source.left with
          | inl sameLocal =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameLocal)
          | inr sameLocal2 =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameLocal2)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameLocal =>
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          exact Or.inl sameLocal
      | inr sameLocal2 =>
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          exact Or.inr sameLocal2
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, sameLower, sameUpper, sameOrder⟩

end BEDC.Derived.ClosedBoundedIntervalUp
