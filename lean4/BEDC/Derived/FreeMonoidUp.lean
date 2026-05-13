import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.MonoidUp

namespace BEDC.Derived.FreeMonoidUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FreeMonoidWordCarrier [AskSetup] [PackageSetup]
    (word route provenance : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory word ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
    Cont word route provenance ∧ PkgSig bundle provenance pkg

theorem FreeMonoidWordCarrier_empty_word_unit [AskSetup] [PackageSetup]
    {word route provenance : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FreeMonoidWordCarrier word route provenance bundle pkg ->
      UnaryHistory BHist.Empty ∧ UnaryHistory word ∧ Cont BHist.Empty word word ∧
        Cont word BHist.Empty word ∧ hsame (append BHist.Empty word) word ∧
          hsame (append word BHist.Empty) word ∧ PkgSig bundle provenance pkg := by
  intro carrier
  rcases carrier with
    ⟨wordUnary, _routeUnary, _provenanceUnary, _wordRouteProvenance, pkgSig⟩
  exact
    ⟨unary_empty, wordUnary, cont_left_unit word, cont_right_unit word,
      append_empty_left word, append_empty_right word, pkgSig⟩

theorem FreeMonoidWordCarrier_concat_associativity [AskSetup] [PackageSetup]
    {u v w uv left vw right route provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FreeMonoidWordCarrier u route provenance bundle pkg ->
      FreeMonoidWordCarrier v route provenance bundle pkg ->
        FreeMonoidWordCarrier w route provenance bundle pkg ->
          Cont u v uv ->
            Cont uv w left ->
              Cont v w vw ->
                Cont u vw right ->
                  PkgSig bundle provenance pkg ->
                    hsame left right := by
  intro _uCarrier _vCarrier _wCarrier uvRow leftRow vwRow rightRow _pkgSig
  unfold Cont at uvRow leftRow vwRow rightRow
  cases uvRow
  cases leftRow
  cases vwRow
  cases rightRow
  exact append_assoc u v w

theorem FreeMonoidWordCarrier_ledger_normal_form [AskSetup] [PackageSetup]
    {word route provenance endpoint : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FreeMonoidWordCarrier word route provenance bundle pkg -> Cont word route endpoint ->
      PkgSig bundle endpoint pkg ->
        UnaryHistory word ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
          UnaryHistory endpoint ∧ Cont word route provenance ∧ Cont word route endpoint ∧
            hsame provenance endpoint ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle endpoint pkg := by
  intro carrier endpointRow endpointSig
  rcases carrier with
    ⟨wordUnary, routeUnary, provenanceUnary, provenanceRow, provenanceSig⟩
  have sameProvenanceEndpoint : hsame provenance endpoint :=
    cont_deterministic provenanceRow endpointRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_transport provenanceUnary sameProvenanceEndpoint
  exact
    ⟨wordUnary, routeUnary, provenanceUnary, endpointUnary, provenanceRow, endpointRow,
      sameProvenanceEndpoint, provenanceSig, endpointSig⟩

theorem FreeMonoidWordCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {word route provenance : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FreeMonoidWordCarrier word route provenance bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          FreeMonoidWordCarrier word route provenance bundle pkg ∧ hsame row provenance)
        (fun row : BHist => Cont word route row ∧ PkgSig bundle row pkg)
        (fun _row : BHist =>
          UnaryHistory word ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
            Cont word route provenance ∧ PkgSig bundle provenance pkg)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro provenance ⟨carrier, hsame_refl provenance⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      rcases sourceRow with ⟨carrierRow, sameRow⟩
      rcases carrierRow with
        ⟨_wordUnary, _routeUnary, _provenanceUnary, provenanceRow, provenanceSig⟩
      cases sameRow
      exact ⟨provenanceRow, provenanceSig⟩
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow.left
  }

theorem FreeMonoidWordCarrier_public_seal [AskSetup] [PackageSetup]
    {word route provenance endpoint u v w uv left vw right : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FreeMonoidWordCarrier word route provenance bundle pkg ->
      Cont word route endpoint ->
        PkgSig bundle endpoint pkg ->
          FreeMonoidWordCarrier u route provenance bundle pkg ->
            FreeMonoidWordCarrier v route provenance bundle pkg ->
              FreeMonoidWordCarrier w route provenance bundle pkg ->
                Cont u v uv ->
                  Cont uv w left ->
                    Cont v w vw ->
                      Cont u vw right ->
                        SemanticNameCert
                            (fun row : BHist =>
                              FreeMonoidWordCarrier word route provenance bundle pkg ∧
                                hsame row provenance)
                            (fun row : BHist => Cont word route row ∧ PkgSig bundle row pkg)
                            (fun _row : BHist =>
                              UnaryHistory word ∧ UnaryHistory route ∧
                                UnaryHistory provenance ∧ Cont word route provenance ∧
                                  PkgSig bundle provenance pkg)
                            hsame ∧
                          UnaryHistory endpoint ∧ hsame provenance endpoint ∧
                            hsame left right ∧ PkgSig bundle provenance pkg ∧
                              PkgSig bundle endpoint pkg := by
  intro carrier endpointRow endpointSig uCarrier vCarrier wCarrier uvRow leftRow vwRow rightRow
  have cert :=
    FreeMonoidWordCarrier_namecert_obligation_surface carrier
  have normal :=
    FreeMonoidWordCarrier_ledger_normal_form carrier endpointRow endpointSig
  rcases normal with
    ⟨_wordUnary, _routeUnary, _provenanceUnary, endpointUnary, _provenanceRow,
      _endpointRow, sameProvenanceEndpoint, provenanceSig, endpointSig'⟩
  have assocSame : hsame left right :=
    FreeMonoidWordCarrier_concat_associativity
      uCarrier vCarrier wCarrier uvRow leftRow vwRow rightRow provenanceSig
  exact
    ⟨cert, endpointUnary, sameProvenanceEndpoint, assocSame, provenanceSig, endpointSig'⟩

theorem FreeMonoidWordCarrier_singleton_concat_inversion [AskSetup] [PackageSetup]
    {u v routeU routeV provenanceU provenanceV : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FreeMonoidWordCarrier u routeU provenanceU bundle pkg ->
      FreeMonoidWordCarrier v routeV provenanceV bundle pkg ->
        Cont u v (BHist.e1 BHist.Empty) ->
          (((hsame v BHist.Empty ∧ hsame u (BHist.e1 BHist.Empty)) ∨
              (hsame u BHist.Empty ∧ hsame v (BHist.e1 BHist.Empty))) ∧
            PkgSig bundle provenanceU pkg ∧ PkgSig bundle provenanceV pkg) := by
  intro uCarrier vCarrier uvSingleton
  rcases uCarrier with ⟨_uUnary, _routeUUnary, _provenanceUUnary, _uRoute, uPkg⟩
  rcases vCarrier with ⟨_vUnary, _routeVUnary, _provenanceVUnary, _vRoute, vPkg⟩
  constructor
  · cases cont_e1_result_inversion uvSingleton with
    | inl base =>
        exact Or.inl ⟨base.left, base.right⟩
    | inr step =>
        rcases step with ⟨vTail, vShape, uTailEmpty⟩
        cases vShape
        have tailsEmpty : u = BHist.Empty ∧ vTail = BHist.Empty :=
          cont_empty_result_inversion uTailEmpty
        cases tailsEmpty.left
        cases tailsEmpty.right
        exact Or.inr ⟨hsame_refl BHist.Empty, hsame_refl (BHist.e1 BHist.Empty)⟩
  · exact ⟨uPkg, vPkg⟩

theorem FreeMonoidWordCarrier_empty_concat_inversion [AskSetup] [PackageSetup]
    {u v uv route provenance : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FreeMonoidWordCarrier u route provenance bundle pkg ->
      FreeMonoidWordCarrier v route provenance bundle pkg ->
        Cont u v uv -> hsame uv BHist.Empty ->
          hsame u BHist.Empty ∧ hsame v BHist.Empty ∧
            UnaryHistory u ∧ UnaryHistory v ∧ PkgSig bundle provenance pkg := by
  intro uCarrier vCarrier uvRow uvEmpty
  obtain ⟨uUnary, _routeUnary, _provenanceUnary, _uRouteProvenance, uPkg⟩ := uCarrier
  obtain ⟨vUnary, _routeUnary', _provenanceUnary', _vRouteProvenance, _vPkg⟩ := vCarrier
  have uvEmptyRow : Cont u v BHist.Empty :=
    cont_result_hsame_transport uvRow uvEmpty
  have factorsEmpty := cont_empty_result_inversion uvEmptyRow
  exact ⟨factorsEmpty.left, factorsEmpty.right, uUnary, vUnary, uPkg⟩

theorem FreeMonoidWordCarrier_list_cont_concrete_instance [AskSetup] [PackageSetup]
    {word route provenance : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FreeMonoidWordCarrier word route provenance bundle pkg ->
      SemanticNameCert UnaryHistory UnaryHistory UnaryHistory
          (BEDC.Derived.MonoidUp.MonoidHistoryClassifier UnaryHistory) ∧
        BEDC.Derived.MonoidUp.MonoidHistoryClassifier UnaryHistory
          (append BHist.Empty word) word ∧
        BEDC.Derived.MonoidUp.MonoidHistoryClassifier UnaryHistory
          (append word BHist.Empty) word ∧
        FreeMonoidWordCarrier word route provenance bundle pkg := by
  intro carrier
  rcases carrier with ⟨wordUnary, routeUnary, provenanceUnary, routeRow, pkgSig⟩
  have monoidData := BEDC.Derived.MonoidUp.unary_append_monoid_semantic_name_certificate
  exact
    ⟨monoidData.left, monoidData.right.left wordUnary,
      monoidData.right.right.left wordUnary,
      ⟨wordUnary, routeUnary, provenanceUnary, routeRow, pkgSig⟩⟩

end BEDC.Derived.FreeMonoidUp
