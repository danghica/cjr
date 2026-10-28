(** Platform-independent account model and invariants. Labels are opaque bytes.
    Repeated labels are allowed; monotonic identifiers distinguish accounts. *)
From Coq Require Import ZArith List Lia Bool.
From cjr.authenticator Require Import model.
Import ListNotations.
Open Scope Z_scope.
Record account := Account {
 account_id : Z; account_label : list Z; account_issuer : list Z;
 account_secret : list Z; account_digits : Z; account_period : Z
}.
Record session := Session { next_id : Z; accounts : list account }.
Definition empty_session := Session 1 [].
Definition account_valid a :=
 1 <= account_id a /\
 (1 <= length (account_label a) <= 128)%nat /\
 (length (account_issuer a) <= 128)%nat /\
 (1 <= length (account_secret a) <= 128)%nat /\
 Forall byte (account_label a) /\ Forall byte (account_issuer a) /\
 Forall byte (account_secret a) /\ valid_parameters (account_digits a) (account_period a).
Definition session_valid s :=
 (length (accounts s) <= 16)%nat /\
 1 <= next_id s <= 9223372036854775807 /\
 NoDup (map account_id (accounts s)) /\
 Forall account_valid (accounts s) /\
 Forall (fun a => account_id a < next_id s) (accounts s).
Definition valid_input label issuer secret digits period :=
 ((1 <=? length label)%nat && (length label <=? 128)%nat &&
 (length issuer <=? 128)%nat && (1 <=? length secret)%nat && (length secret <=? 128)%nat &&
 forallb (fun x => (0 <=? x) && (x <? 256)) label &&
 forallb (fun x => (0 <=? x) && (x <? 256)) issuer &&
 forallb (fun x => (0 <=? x) && (x <? 256)) secret &&
 ((digits =? 6) || (digits =? 8)) && (1 <=? period) && (period <=? 2147483647))%bool.
Definition enroll s label issuer secret digits period : Z * session :=
 if valid_input label issuer secret digits period then
 if (length (accounts s) <? 16)%nat then
 if next_id s <=? 9223372036854775806 then
 (next_id s, Session (next_id s + 1)
  (accounts s ++ [Account (next_id s) label issuer secret digits period]))
 else (-3,s) else (-2,s) else (-1,s).
Definition remove_account s id :=
 Session (next_id s) (filter (fun a => negb (account_id a =? id)) (accounts s)).
Definition find_account s id := find (fun a => account_id a =? id) (accounts s).
Definition code_for s id timestamp :=
 match find_account s id with
 | None => None
 | Some a => if 0 <=? timestamp then Some (totp (account_secret a) timestamp (account_period a) (account_digits a)) else None
 end.
Definition metadata a := (account_id a, account_label a, account_issuer a, account_digits a, account_period a).
Theorem empty_session_valid : session_valid empty_session.
Proof. unfold session_valid, empty_session; simpl. repeat split; try constructor; lia. Qed.
Lemma byte_check_spec xs :
 forallb (fun x => (0 <=? x) && (x <? 256)) xs = true <-> Forall byte xs.
Proof.
 rewrite forallb_forall, Forall_forall. split; intros H x Hx; specialize (H x Hx).
 - apply andb_true_iff in H as [H0 H1]. apply Z.leb_le in H0. apply Z.ltb_lt in H1. exact (conj H0 H1).
 - unfold byte in H. apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.
Lemma valid_input_spec label issuer secret digits period :
 valid_input label issuer secret digits period = true ->
 forall id, 1 <= id -> account_valid (Account id label issuer secret digits period).
Proof.
 unfold valid_input. repeat rewrite andb_true_iff.
 intros [[[[[[[[[[Hl Hlm] Him] Hs] Hsm] Hlb] Hib] Hsb] Hd] Hp] Hpm] id Hid.
 apply Nat.leb_le in Hl,Hlm,Him,Hs,Hsm.
 apply byte_check_spec in Hlb,Hib,Hsb. apply orb_true_iff in Hd.
 apply Z.leb_le in Hp,Hpm. unfold account_valid, valid_parameters; simpl.
 repeat split; try assumption; try lia.
Qed.
(** The application contract assumes a valid session, including positive IDs. *)
Theorem enroll_failure_atomic s label issuer secret digits period code s' :
 session_valid s -> enroll s label issuer secret digits period = (code,s') -> code < 0 -> s' = s.
Proof.
 intros [Hlen [Hnext Hrest]]. unfold enroll.
 destruct (valid_input label issuer secret digits period);
 destruct (length (accounts s) <? 16)%nat;
 destruct (next_id s <=? 9223372036854775806); intros H Hc;
 inversion H; subst; try reflexivity; lia.
Qed.
Theorem enroll_preserves_validity s label issuer secret digits period code s' :
 session_valid s -> enroll s label issuer secret digits period = (code,s') -> session_valid s'.
Proof.
 intros Hvalid. unfold enroll.
 destruct (valid_input label issuer secret digits period) eqn:Hi; [|intros H; inversion H; subst; exact Hvalid].
 destruct (length (accounts s) <? 16)%nat eqn:Hroom; [|intros H; inversion H; subst; exact Hvalid].
 destruct (next_id s <=? 9223372036854775806) eqn:Hnext; [|intros H; inversion H; subst; exact Hvalid].
 intros H. inversion H; subst s'.
 destruct Hvalid as [Hlen [Hid [Hdup [Hav Hlt]]]].
 apply Nat.ltb_lt in Hroom. apply Z.leb_le in Hnext.
 unfold session_valid; simpl. rewrite length_app; simpl.
 split; [lia|]. split; [lia|]. split.
 - rewrite map_app. simpl. apply NoDup_app. repeat split; auto.
   + constructor; [simpl; tauto|constructor].
   + intros id Hin Hsingle. simpl in Hsingle. destruct Hsingle as [<-|Hsingle]; [|contradiction].
     apply in_map_iff in Hin as [a [Ha Hin]].
     rewrite Forall_forall in Hlt. specialize (Hlt a Hin). lia.
 - split.
   + apply Forall_app. split; [assumption|]. constructor; [eapply valid_input_spec; eauto; lia|constructor].
   + apply Forall_app. split.
     * eapply Forall_impl; [|exact Hlt]. simpl; intros; lia.
     * constructor; [simpl; lia|constructor].
Qed.
Theorem remove_preserves_validity s id : session_valid s -> session_valid (remove_account s id).
Proof.
 intros [Hlen [Hnext [Hdup [Hav Hlt]]]]. unfold session_valid, remove_account; simpl.
 split; [pose proof (filter_length_le (fun a => negb (account_id a =? id)) (accounts s)); lia|].
 split; [assumption|]. split.
 - assert (Hmap : forall xs, map account_id (filter (fun a => negb (account_id a =? id)) xs) =
       filter (fun x => negb (x =? id)) (map account_id xs)).
   { induction xs as [|a xs IH]; simpl; [reflexivity|].
     destruct (negb (account_id a =? id)); simpl; rewrite IH; reflexivity. }
   rewrite Hmap. apply NoDup_filter. exact Hdup.
 - split; apply Forall_forall; intros a Hin; apply filter_In in Hin as [Hin _];
     rewrite Forall_forall in *; auto.
Qed.
Theorem removed_account_absent s id : find_account (remove_account s id) id = None.
Proof.
 unfold find_account, remove_account; simpl.
 induction (accounts s) as [|a xs IH]; simpl; [reflexivity|].
 destruct (account_id a =? id) eqn:E; simpl; [exact IH|].
 rewrite E. exact IH.
Qed.
