import BEDC.Derived.BedcSelfSubstrateUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BedcSelfSubstrateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BedcSelfSubstratePacket [AskSetup] [PackageSetup]
    (generators equality recursors purity boundary transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory generators ∧ UnaryHistory equality ∧ UnaryHistory recursors ∧
    UnaryHistory purity ∧ UnaryHistory boundary ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont generators equality recursors ∧ Cont purity boundary transport ∧
          Cont transport route provenance ∧ PkgSig bundle name pkg ∧
            PkgSig bundle provenance pkg

theorem BedcSelfSubstrateObligationSurface [AskSetup] [PackageSetup]
    {generators equality recursors purity boundary transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BedcSelfSubstratePacket generators equality recursors purity boundary transport route
        provenance name bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          BedcSelfSubstratePacket generators equality recursors purity boundary transport route
              provenance name bundle pkg ∧
            (hsame row generators ∨ hsame row equality ∨ hsame row recursors ∨
              hsame row purity ∨ hsame row boundary))
        (fun _row : BHist =>
          Cont generators equality recursors ∧ Cont purity boundary transport ∧
            Cont transport route provenance ∧ PkgSig bundle provenance pkg)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet
  have packetWitness := packet
  obtain ⟨generatorsUnary, equalityUnary, recursorsUnary, purityUnary, boundaryUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, generatorsEqualityRecursors,
    purityBoundaryTransport, transportRouteProvenance, namePkg, provenancePkg⟩ := packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro generators
          ⟨packetWitness, Or.inl (hsame_refl generators)⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        constructor
        · exact source.left
        · cases source.right with
          | inl sameGenerators =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameGenerators)
          | inr rest =>
              cases rest with
              | inl sameEquality =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameEquality))
              | inr rest =>
                  cases rest with
                  | inl sameRecursors =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRecursors)))
                  | inr rest =>
                      cases rest with
                      | inl samePurity =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) samePurity))))
                      | inr sameBoundary =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (hsame_trans (hsame_symm sameRows) sameBoundary))))
    }
    pattern_sound := by
      intro _row _source
      exact
        ⟨generatorsEqualityRecursors, purityBoundaryTransport, transportRouteProvenance,
          provenancePkg⟩
    ledger_sound := by
      intro row source
      have rowUnary : UnaryHistory row := by
        cases source.right with
        | inl sameGenerators =>
            exact unary_transport generatorsUnary (hsame_symm sameGenerators)
        | inr rest =>
            cases rest with
            | inl sameEquality =>
                exact unary_transport equalityUnary (hsame_symm sameEquality)
            | inr rest =>
                cases rest with
                | inl sameRecursors =>
                    exact unary_transport recursorsUnary (hsame_symm sameRecursors)
                | inr rest =>
                    cases rest with
                    | inl samePurity =>
                        exact unary_transport purityUnary (hsame_symm samePurity)
                    | inr sameBoundary =>
                        exact unary_transport boundaryUnary (hsame_symm sameBoundary)
      exact ⟨rowUnary, namePkg, provenancePkg⟩
  }

end BEDC.Derived.BedcSelfSubstrateUp
