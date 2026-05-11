import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BousfieldLocalizationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BousfieldLocalizationPacket [AskSetup] [PackageSetup]
    (model selected localObjects route provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory model ∧ UnaryHistory selected ∧ UnaryHistory localObjects ∧
    UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory ledger ∧
      UnaryHistory endpoint ∧ Cont model selected route ∧
        Cont route localObjects endpoint ∧ PkgSig bundle endpoint pkg

theorem BousfieldLocalizationPacket_local_object_handoff [AskSetup] [PackageSetup]
    {model selected localObjects route provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BousfieldLocalizationPacket model selected localObjects route provenance ledger endpoint
        bundle pkg ->
      UnaryHistory model ∧ UnaryHistory selected ∧ UnaryHistory localObjects ∧
        UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory ledger ∧
          UnaryHistory endpoint ∧ Cont model selected route ∧
            Cont route localObjects endpoint ∧ hsame route (append model selected) ∧
              hsame endpoint (append route localObjects) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have modelUnary : UnaryHistory model :=
    packet.left
  have selectedUnary : UnaryHistory selected :=
    packet.right.left
  have localObjectsUnary : UnaryHistory localObjects :=
    packet.right.right.left
  have routeUnary : UnaryHistory route :=
    packet.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    packet.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    packet.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    packet.right.right.right.right.right.right.left
  have routeRow : Cont model selected route :=
    packet.right.right.right.right.right.right.right.left
  have endpointRow : Cont route localObjects endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right
  exact
    ⟨modelUnary,
      selectedUnary,
      localObjectsUnary,
      routeUnary,
      provenanceUnary,
      ledgerUnary,
      endpointUnary,
      routeRow,
      endpointRow,
      routeRow,
      endpointRow,
      pkgSig⟩

def BousfieldLocalizationFinitePacket [AskSetup] [PackageSetup]
    (model selected localObj classifier provenance ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory model ∧ UnaryHistory selected ∧ UnaryHistory localObj ∧
    UnaryHistory classifier ∧ UnaryHistory provenance ∧ UnaryHistory ledger ∧
      Cont model selected classifier ∧ Cont selected localObj ledger ∧ PkgSig bundle ledger pkg

theorem BousfieldLocalizationFinitePacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {model selected localObj classifier provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BousfieldLocalizationFinitePacket model selected localObj classifier provenance ledger
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          BousfieldLocalizationFinitePacket model selected localObj classifier provenance ledger
              bundle pkg ∧ hsame row ledger)
        (fun row : BHist =>
          BousfieldLocalizationFinitePacket model selected localObj classifier provenance ledger
              bundle pkg ∧ hsame row ledger)
        (fun row : BHist =>
          BousfieldLocalizationFinitePacket model selected localObj classifier provenance ledger
              bundle pkg ∧ hsame row ledger)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro ledger ⟨packet, hsame_refl ledger⟩
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' same carrier
        exact ⟨carrier.left, hsame_trans (hsame_symm same) carrier.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

def BousfieldLocalizationFiniteLocalizingPacket [AskSetup] [PackageSetup]
    (model selected localObjects transport provenance certRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory model ∧ UnaryHistory selected ∧ UnaryHistory localObjects ∧
    UnaryHistory transport ∧ UnaryHistory provenance ∧ UnaryHistory certRow ∧
      Cont model selected transport ∧ Cont transport provenance certRow ∧
        PkgSig bundle certRow pkg ∧ hsame model certRow ∧ hsame selected certRow ∧
          hsame localObjects certRow ∧ hsame transport certRow ∧
            hsame provenance certRow

theorem BousfieldLocalizationFiniteLocalizingPacket_namecert_obligations
    [AskSetup] [PackageSetup]
    {model selected localObjects transport provenance certRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BousfieldLocalizationFiniteLocalizingPacket model selected localObjects transport
        provenance certRow bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row model ∨ hsame row selected ∨ hsame row localObjects ∨
              hsame row transport ∨ hsame row provenance ∨ hsame row certRow)
          (fun row : BHist =>
            hsame row transport ∨ hsame row provenance ∨ hsame row certRow)
          (fun row : BHist => hsame row certRow)
          hsame ∧
        Cont model selected transport ∧ Cont transport provenance certRow ∧
          PkgSig bundle certRow pkg := by
  intro packet
  obtain ⟨_modelUnary, _selectedUnary, _localObjectsUnary, _transportUnary,
    _provenanceUnary, _certUnary, modelSelectedTransport, transportProvenanceCert,
    packageCert, modelCert, selectedCert, localObjectsCert, transportCert,
    provenanceCert⟩ := packet
  have certRowSource :
      hsame certRow model ∨ hsame certRow selected ∨ hsame certRow localObjects ∨
        hsame certRow transport ∨ hsame certRow provenance ∨ hsame certRow certRow :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl certRow)))))
  have sourceToCert :
      forall {row : BHist},
        (hsame row model ∨ hsame row selected ∨ hsame row localObjects ∨
          hsame row transport ∨ hsame row provenance ∨ hsame row certRow) ->
          hsame row certRow := by
    intro row source
    cases source with
    | inl sameModel =>
        exact hsame_trans sameModel modelCert
    | inr source =>
        cases source with
        | inl sameSelected =>
            exact hsame_trans sameSelected selectedCert
        | inr source =>
            cases source with
            | inl sameLocalObjects =>
                exact hsame_trans sameLocalObjects localObjectsCert
            | inr source =>
                cases source with
                | inl sameTransport =>
                    exact hsame_trans sameTransport transportCert
                | inr source =>
                    cases source with
                    | inl sameProvenance =>
                        exact hsame_trans sameProvenance provenanceCert
                    | inr sameCert =>
                        exact sameCert
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row model ∨ hsame row selected ∨ hsame row localObjects ∨
              hsame row transport ∨ hsame row provenance ∨ hsame row certRow)
          (fun row : BHist =>
            hsame row transport ∨ hsame row provenance ∨ hsame row certRow)
          (fun row : BHist => hsame row certRow)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro certRow certRowSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' same source
        cases source with
        | inl sameModel =>
            exact Or.inl (hsame_trans (hsame_symm same) sameModel)
        | inr source =>
            cases source with
            | inl sameSelected =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) sameSelected))
            | inr source =>
                cases source with
                | inl sameLocalObjects =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm same) sameLocalObjects)))
                | inr source =>
                    cases source with
                    | inl sameTransport =>
                        exact Or.inr (Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm same) sameTransport))))
                    | inr source =>
                        cases source with
                        | inl sameProvenance =>
                            exact Or.inr (Or.inr (Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm same) sameProvenance)))))
                        | inr sameCert =>
                            exact Or.inr (Or.inr (Or.inr
                              (Or.inr (Or.inr (hsame_trans (hsame_symm same) sameCert)))))
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (sourceToCert source))
    ledger_sound := by
      intro _row source
      exact sourceToCert source
  }
  exact ⟨cert, modelSelectedTransport, transportProvenanceCert, packageCert⟩

theorem BousfieldLocalizationEmptySelectedMap_boundary [AskSetup] [PackageSetup]
    {model selected localRow transport provenance certRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory model -> UnaryHistory localRow -> UnaryHistory provenance ->
      hsame selected BHist.Empty -> Cont model selected transport ->
        Cont transport localRow certRow -> PkgSig bundle certRow pkg ->
          hsame transport model ∧ UnaryHistory certRow ∧
            Cont transport localRow certRow ∧ PkgSig bundle certRow pkg := by
  intro modelUnary localUnary _provenanceUnary selectedEmpty transportRow certRowCont pkgSig
  cases selectedEmpty
  have transportSame : hsame transport model :=
    cont_deterministic transportRow (cont_right_unit model)
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed modelUnary unary_empty transportRow
  have certRowUnary : UnaryHistory certRow :=
    unary_cont_closed transportUnary localUnary certRowCont
  exact And.intro transportSame
    (And.intro certRowUnary (And.intro certRowCont pkgSig))

end BEDC.Derived.BousfieldLocalizationUp
