import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.HaltingDistinctionLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HaltingDistinctionLimitCarrier [AskSetup] [PackageSetup]
    (program input trace diagonal transport route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory program ∧ UnaryHistory input ∧ UnaryHistory trace ∧
    UnaryHistory diagonal ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont input trace diagonal ∧
        Cont diagonal transport route ∧ Cont route provenance nameRow ∧
          hsame diagonal (append input trace) ∧ PkgSig bundle nameRow pkg

theorem HaltingDistinctionLimitCarrier_route_surface [AskSetup] [PackageSetup]
    {program input trace diagonal transport route provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionLimitCarrier program input trace diagonal transport route provenance
        nameRow bundle pkg ->
      UnaryHistory diagonal ∧ UnaryHistory route ∧ UnaryHistory nameRow ∧
        Cont input trace diagonal ∧ Cont diagonal transport route ∧
          Cont route provenance nameRow ∧ hsame diagonal (append input trace) ∧
            PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier
  obtain ⟨_programUnary, _inputUnary, _traceUnary, diagonalUnary, _transportUnary,
    routeUnary, _provenanceUnary, nameRowUnary, inputTraceDiagonal,
    diagonalTransportRoute, routeProvenanceNameRow, sameDiagonal, namePkg⟩ := carrier
  exact
    ⟨diagonalUnary, routeUnary, nameRowUnary, inputTraceDiagonal,
      diagonalTransportRoute, routeProvenanceNameRow, sameDiagonal, namePkg⟩

theorem HaltingDistinctionLimitPublicBoundary [AskSetup] [PackageSetup]
    {program input trace diagonal transport route provenance nameRow publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionLimitCarrier program input trace diagonal transport route provenance
        nameRow bundle pkg →
      Cont route nameRow publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row program ∨ hsame row input ∨ hsame row trace ∨
                  hsame row diagonal ∨ hsame row publicRead)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
              hsame ∧ UnaryHistory publicRead ∧ Cont input trace diagonal ∧
            Cont diagonal transport route ∧ Cont route nameRow publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier publicRoute publicPkg
  obtain ⟨programUnary, inputUnary, traceUnary, diagonalUnary, transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, inputTraceDiagonal, diagonalTransportRoute,
    _routeProvenanceNameRow, _sameDiagonal, _namePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routeUnary nameRowUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row program ∨ hsame row input ∨ hsame row trace ∨
              hsame row diagonal ∨ hsame row publicRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, publicPkg⟩
  }
  exact
    ⟨cert, publicUnary, inputTraceDiagonal, diagonalTransportRoute, publicRoute⟩

theorem HaltingDistinctionLimitCarrier_bridge_boundary [AskSetup] [PackageSetup]
    {program input trace diagonal transport route provenance nameRow bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionLimitCarrier program input trace diagonal transport route provenance
        nameRow bundle pkg ->
      Cont nameRow provenance bridgeRead ->
        Cont input (append trace (append transport (append provenance provenance))) bridgeRead ∧
          hsame nameRow nameRow ∧ PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier bridgeRoute
  obtain ⟨_programUnary, _inputUnary, _traceUnary, _diagonalUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, inputTraceDiagonal,
    diagonalTransportRoute, routeProvenanceNameRow, _sameDiagonal, namePkg⟩ := carrier
  cases inputTraceDiagonal
  cases diagonalTransportRoute
  cases routeProvenanceNameRow
  cases bridgeRoute
  constructor
  · exact
      Eq.trans (append_assoc (append (append input trace) transport) provenance provenance)
        (Eq.trans (append_assoc (append input trace) transport (append provenance provenance))
          (append_assoc input trace (append transport (append provenance provenance))))
  · constructor
    · exact hsame_refl (append (append (append input trace) transport) provenance)
    · exact namePkg

end BEDC.Derived.HaltingDistinctionLimitUp
