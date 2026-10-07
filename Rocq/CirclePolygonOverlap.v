(** * Overlap Area Between Circle and Square

    Formal verification of the area of intersection between a circle of radius R
    and a square with side length 2s, both centered at the origin.

    With both shapes centred there are exactly three regimes:
    - |R| <= s          : the disc lies inside the square, area πR²
    - s < |R| <= s√2    : each of the four edges cuts a circular cap off the
                          disc, area πR² - 4·segment(R, s)
    - s√2 < |R|         : the square lies inside the disc, area (2s)²

    The eight cases drawn in
    ../Rough/Area of overlap between circle and square - 2D (Tidy Working).png
    describe a circle whose centre moves relative to the square; that
    position-dependent problem is not formalised here.

    Main results:
    - [overlap_area_double_integral]: [overlap_area R s] is the double integral
      over the square of the indicator function of [in_overlap R s].
    - [overlap_area_nonneg], [overlap_area_bounded]: 0 <= area <= min(πR², 4s²).
    - [overlap_area_continuous]: the area is jointly continuous in R and s.

    Integrals are Coquelicot's Riemann integrals ([is_RInt]). Nothing is
    admitted and the file declares no axioms; [Print Assumptions] reports only
    the standard library's classical-reals axioms plus functional
    extensionality and excluded middle, which Coquelicot relies on.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Coquelicot Require Import Coquelicot.
Open Scope R_scope.

(** ** Basic geometric definitions *)

(** Circle centered at origin with radius R *)
Definition in_circle (r : R) (x : R) (y : R) : Prop :=
  x * x + y * y <= r * r.

(** Square centered at origin with half-side s (full side length 2s) *)
Definition in_square (s : R) (x : R) (y : R) : Prop :=
  -s <= x <= s /\ -s <= y <= s.

(** The overlap region *)
Definition in_overlap (r : R) (s : R) (x : R) (y : R) : Prop :=
  in_circle r x y /\ in_square s x y.

(** ** Sector and triangle area formulas *)

(** Area of circular sector with central angle θ and radius r *)
Definition sector_area (r : R) (theta : R) : R :=
  (1/2) * r * r * theta.

(** Area of triangle with base b and height h *)
Definition triangle_area (b : R) (h : R) : R :=
  (1/2) * b * h.

(** Circular segment: sector minus inscribed triangle
    For a chord at distance d from center of circle radius R:
    - angle = 2 * arccos(d/R)
    - chord_half_length = sqrt(R² - d²)
*)
Definition segment_area (r : R) (d : R) : R :=
  let angle := 2 * acos (d / r) in
  let chord_half := sqrt (r * r - d * d) in
  sector_area r angle - triangle_area (2 * chord_half) d.

(** ** The overlap area *)

(** [in_circle r] only depends on r², so a negative radius describes the
    circle of radius |r|; a negative half-side describes the empty square. *)
Definition overlap_area (r : R) (s : R) : R :=
  let a := Rabs r in
  if Rle_dec s 0 then 0                          (** empty (or one-point) square *)
  else if Rle_dec a s then PI * a * a            (** disc inside the square *)
  else if Rle_dec a (s * sqrt 2) then
    PI * a * a - 4 * segment_area a s            (** four caps cut off *)
  else (2 * s) * (2 * s).                        (** square inside the disc *)

(** ** Vertical slices of the overlap region *)

(** For -s <= x <= s the overlap meets the vertical line at abscissa x in the
    segment [-slice r s x, slice r s x] when x² <= r², and nowhere otherwise
    (where [slice r s x] is 0). Either way the slice has length 2·slice. *)
Definition slice (r s x : R) : R := Rmin s (sqrt (r * r - x * x)).

Lemma slice_bounds : forall r s x, 0 <= s -> 0 <= slice r s x <= s.
Proof.
  intros r s x Hs. unfold slice. split.
  - apply Rmin_glb; [exact Hs | apply sqrt_pos].
  - apply Rmin_l.
Qed.

Lemma in_overlap_slice : forall r s x y, -s <= x <= s -> x * x <= r * r ->
  (in_overlap r s x y <-> - slice r s x <= y <= slice r s x).
Proof.
  intros r s x y Hx Hxr.
  set (v := r * r - x * x).
  assert (Hv : 0 <= v) by (unfold v; lra).
  pose proof (sqrt_sqrt v Hv) as Hvv. pose proof (sqrt_pos v) as Hv0.
  unfold in_overlap, in_circle, in_square, slice. fold v. split.
  - intros [Hc [_ Hy]].
    assert (Hyv : Rabs y <= sqrt v).
    { rewrite <- sqrt_Rsqr_abs. apply sqrt_le_1_alt. unfold Rsqr, v. lra. }
    unfold Rmin. destruct (Rle_dec s (sqrt v));
      unfold Rabs in Hyv; destruct (Rcase_abs y); lra.
  - intros Hy. pose proof (Rmin_l s (sqrt v)). pose proof (Rmin_r s (sqrt v)).
    split; [|split; [exact Hx | lra]].
    assert (y * y <= v) by nra. unfold v in *. lra.
Qed.

Lemma not_in_overlap_far : forall r s x y, r * r < x * x -> ~ in_overlap r s x y.
Proof.
  intros r s x y Hxr [Hc _]. unfold in_circle in Hc. nra.
Qed.

Lemma slice_far : forall a s x, 0 <= s -> a * a <= x * x -> slice a s x = 0.
Proof.
  intros a s x Hs Hx. unfold slice. rewrite sqrt_neg_0 by lra.
  apply Rmin_right. exact Hs.
Qed.

(** ** Integration toolkit (specialised to real-valued functions) *)

Lemma is_RInt_ext_le : forall (f g : R -> R) a b l, a <= b ->
  (forall x, a < x < b -> f x = g x) -> is_RInt f a b l -> is_RInt g a b l.
Proof.
  intros f g a b l Hab Hfg Hf. apply (is_RInt_ext f); [|exact Hf].
  intros x Hx. rewrite Rmin_left, Rmax_right in Hx by lra. apply Hfg, Hx.
Qed.

Lemma is_RInt_const_R : forall a b c : R, is_RInt (fun _ => c) a b ((b - a) * c).
Proof. intros a b c. apply (is_RInt_const a b c). Qed.

Lemma is_RInt_Chasles_R : forall (f : R -> R) a b c l1 l2,
  is_RInt f a b l1 -> is_RInt f b c l2 -> is_RInt f a c (l1 + l2).
Proof. intros. apply (is_RInt_Chasles f a b c l1 l2); assumption. Qed.

Lemma is_RInt_scal_R : forall (f : R -> R) a b k l,
  is_RInt f a b l -> is_RInt (fun x => k * f x) a b (k * l).
Proof. intros. apply (is_RInt_scal f a b k l). assumption. Qed.

Lemma is_RInt_minus_R : forall (f g : R -> R) a b lf lg,
  is_RInt f a b lf -> is_RInt g a b lg -> is_RInt (fun x => f x - g x) a b (lf - lg).
Proof. intros. apply (is_RInt_minus f g a b lf lg); assumption. Qed.

(** An integrand trapped between m and M has integral between (b-a)m and (b-a)M. *)
Lemma is_RInt_bound : forall (f : R -> R) a b l m M, a <= b -> is_RInt f a b l ->
  (forall x, a < x < b -> m <= f x <= M) -> (b - a) * m <= l <= (b - a) * M.
Proof.
  intros f a b l m M Hab Hf Hb.
  assert (Hex : ex_RInt f a b) by (exists l; exact Hf).
  assert (Hl : RInt f a b = l) by (apply is_RInt_unique; exact Hf).
  assert (Hm : RInt (fun _ => m) a b = (b - a) * m)
    by (apply is_RInt_unique; apply is_RInt_const_R).
  assert (HM : RInt (fun _ => M) a b = (b - a) * M)
    by (apply is_RInt_unique; apply is_RInt_const_R).
  rewrite <- Hl, <- Hm, <- HM. split.
  - apply RInt_le; [exact Hab | apply ex_RInt_const | exact Hex | intros x Hx; apply Hb, Hx].
  - apply RInt_le; [exact Hab | exact Hex | apply ex_RInt_const | intros x Hx; apply Hb, Hx].
Qed.

Lemma continuous_of_ex_derive : forall (f : R -> R) x, ex_derive f x -> continuous f x.
Proof.
  intros f x H. apply (ex_derive_continuous (K := R_AbsRing) (V := R_NormedModule)). exact H.
Qed.

(** ** Square roots and arcsines *)

Lemma sqrt_le_of_le_sq : forall v s, 0 <= s -> v <= s * s -> sqrt v <= s.
Proof.
  intros v s Hs Hv. apply Rle_trans with (sqrt (s * s)).
  - apply sqrt_le_1_alt. exact Hv.
  - rewrite sqrt_square by exact Hs. lra.
Qed.

Lemma le_sqrt_of_sq_le : forall v s, 0 <= s -> s * s <= v -> s <= sqrt v.
Proof.
  intros v s Hs Hv. apply Rle_trans with (sqrt (s * s)).
  - rewrite sqrt_square by exact Hs. lra.
  - apply sqrt_le_1_alt. exact Hv.
Qed.

Lemma sqrt_r2_minus : forall r u, 0 < r -> -1 <= u <= 1 ->
  r * sqrt (1 - u²) = sqrt (r * r - (r * u) * (r * u)).
Proof.
  intros r u Hr Hu.
  replace (r * r - (r * u) * (r * u)) with ((r * r) * (1 - u²)) by (unfold Rsqr; ring).
  rewrite sqrt_mult_alt by nra.
  rewrite sqrt_square by lra. reflexivity.
Qed.

Lemma sqrt2_sq : sqrt 2 * sqrt 2 = 2.
Proof. apply sqrt_sqrt. lra. Qed.

Lemma le_s_sqrt2 : forall a s, 0 <= a -> 0 <= s ->
  (a <= s * sqrt 2 <-> a * a <= 2 * (s * s)).
Proof.
  intros a s Ha Hs.
  assert (Hq : (s * sqrt 2) * (s * sqrt 2) = 2 * (s * s)).
  { replace ((s * sqrt 2) * (s * sqrt 2)) with (s * s * (sqrt 2 * sqrt 2)) by ring.
    rewrite sqrt2_sq. ring. }
  assert (Hq0 : 0 <= s * sqrt 2) by (apply Rmult_le_pos; [lra | apply sqrt_pos]).
  split; intro Hle.
  - rewrite <- Hq. apply Rmult_le_compat; assumption.
  - destruct (Rle_lt_dec a (s * sqrt 2)) as [H'|H']; [exact H'|].
    exfalso. assert ((s * sqrt 2) * (s * sqrt 2) < a * a)
      by (apply Rmult_le_0_lt_compat; assumption).
    lra.
Qed.

Lemma asin_nonneg : forall u, 0 <= u -> 0 <= asin u.
Proof.
  intros u Hu. destruct (Rle_lt_dec 0 (asin u)) as [H|H]; [exact H|].
  exfalso. pose proof (asin_bound u) as Hb.
  assert (Hs : sin (asin u) < 0) by (apply sin_lt_0_var; pose proof PI_RGT_0; lra).
  destruct (Rle_lt_dec u 1) as [Hu1|Hu1].
  - rewrite sin_asin in Hs by lra. lra.
  - unfold asin in H. destruct (Rle_dec u (-1)); [lra|].
    destruct (Rle_dec 1 u); [pose proof PI_RGT_0; lra | lra].
Qed.

Lemma asin_complement : forall u, 0 <= u <= 1 ->
  asin (sqrt (1 - u²)) = PI / 2 - asin u.
Proof.
  intros u Hu.
  rewrite <- cos_asin by lra. rewrite <- sin_shift.
  apply asin_sin. pose proof (asin_bound u). pose proof (asin_nonneg u (proj1 Hu)).
  pose proof PI_RGT_0. lra.
Qed.

(** ** Area under a circular arc *)

(** An antiderivative of x ↦ √(r² - x²) on [-r, r]. *)
Definition circle_primitive (r x : R) : R :=
  (x * sqrt (r * r - x * x) + r * r * asin (x / r)) / 2.

Lemma circle_primitive_opp : forall r x,
  circle_primitive r (- x) = - circle_primitive r x.
Proof.
  intros r x. unfold circle_primitive.
  replace (- x / r) with (- (x / r)) by (unfold Rdiv; ring).
  rewrite asin_opp. replace (- x * - x) with (x * x) by ring. field.
Qed.

Lemma circle_primitive_edge : forall r, 0 < r -> circle_primitive r r = PI * r * r / 4.
Proof.
  intros r Hr. unfold circle_primitive.
  replace (r * r - r * r) with 0 by ring. rewrite sqrt_0.
  replace (r / r) with 1 by (field; lra). rewrite asin_1. field.
Qed.

(** ∫ₐᵇ √(r² - x²) dx, proved by the substitution x = r·sin t, which keeps the
    integrand smooth even when a or b is ±r. *)
Lemma is_RInt_circle : forall r a b, 0 < r ->
  -r <= a <= r -> -r <= b <= r ->
  is_RInt (fun x => sqrt (r * r - x * x)) a b
          (circle_primitive r b - circle_primitive r a).
Proof.
  intros r a b Hr Ha Hb.
  set (f := fun x => sqrt (r * r - x * x)).
  set (al := asin (a / r)). set (be := asin (b / r)).
  assert (Har : -1 <= a / r <= 1).
  { split; [apply (Rmult_le_reg_r r); [lra|]; field_simplify; lra
           |apply (Rmult_le_reg_r r); [lra|]; field_simplify; lra]. }
  assert (Hbr : -1 <= b / r <= 1).
  { split; [apply (Rmult_le_reg_r r); [lra|]; field_simplify; lra
           |apply (Rmult_le_reg_r r); [lra|]; field_simplify; lra]. }
  assert (Hf : forall z, continuous f z).
  { intro z. unfold f. apply continuous_sqrt_comp.
    apply continuous_of_ex_derive. auto_derive. auto. }
  (* change of variables x = r sin t *)
  assert (Hcomp := is_RInt_comp f (fun t => r * sin t) (fun t => r * cos t) al be
                     (fun x _ => Hf _)).
  assert (Hg : forall x, Rmin al be <= x <= Rmax al be ->
            is_derive (fun t => r * sin t) x (r * cos x) /\ continuous (fun t => r * cos t) x).
  { intros x _. split.
    - auto_derive; [auto | ring].
    - apply continuous_of_ex_derive. auto_derive. auto. }
  specialize (Hcomp Hg).
  assert (Hga : r * sin al = a) by (unfold al; rewrite sin_asin by exact Har; field; lra).
  assert (Hgb : r * sin be = b) by (unfold be; rewrite sin_asin by exact Hbr; field; lra).
  cbv beta in Hcomp. rewrite Hga, Hgb in Hcomp.
  (* the transformed integrand r² cos² t has an elementary antiderivative *)
  set (H := fun t => r * r * (t + sin t * cos t) / 2).
  assert (Hder : is_RInt (fun t => r * r * (cos t * cos t)) al be (H be - H al)).
  { apply (is_RInt_derive H).
    - intros x _. unfold H. auto_derive; [auto|].
      pose proof (sin2_cos2 x) as Hsc. unfold Rsqr in Hsc. nra.
    - intros x _. apply continuous_of_ex_derive. auto_derive. auto. }
  assert (Hrange : forall t, Rmin al be < t < Rmax al be -> 0 <= cos t).
  { intros t Ht. pose proof (asin_bound (a / r)). pose proof (asin_bound (b / r)).
    fold al be in H0, H1.
    apply cos_ge_0.
    - apply Rle_trans with (Rmin al be); [apply Rmin_glb; lra | lra].
    - apply Rle_trans with (Rmax al be); [lra | apply Rmax_lub; lra]. }
  assert (Hext : is_RInt (fun y => scal (r * cos y) (f (r * sin y))) al be (H be - H al)).
  { apply (is_RInt_ext (fun t => r * r * (cos t * cos t))); [|exact Hder].
    intros t Ht. specialize (Hrange t Ht). unfold f, scal; simpl. unfold mult; simpl.
    replace (r * r - r * sin t * (r * sin t)) with ((r * cos t) * (r * cos t)).
    2:{ pose proof (sin2_cos2 t) as Hsc. unfold Rsqr in Hsc. nra. }
    rewrite sqrt_square by nra. ring. }
  assert (E1 : RInt (fun y => scal (r * cos y) (f (r * sin y))) al be = RInt f a b)
    by (apply is_RInt_unique; exact Hcomp).
  assert (E2 : RInt (fun y => scal (r * cos y) (f (r * sin y))) al be = H be - H al)
    by (apply is_RInt_unique; exact Hext).
  assert (Hval : RInt f a b = H be - H al) by congruence.
  assert (Hex : ex_RInt f a b)
    by (apply (ex_RInt_continuous (V := R_CompleteNormedModule)); intros; apply Hf).
  apply (RInt_correct (V := R_CompleteNormedModule)) in Hex. rewrite Hval in Hex.
  replace (circle_primitive r b - circle_primitive r a) with (H be - H al); [exact Hex|].
  assert (Sa : sqrt (r * r - a * a) = r * sqrt (1 - (a / r)²)).
  { rewrite (sqrt_r2_minus r (a / r)) by assumption.
    replace (r * (a / r)) with a by (field; lra). reflexivity. }
  assert (Sb : sqrt (r * r - b * b) = r * sqrt (1 - (b / r)²)).
  { rewrite (sqrt_r2_minus r (b / r)) by assumption.
    replace (r * (b / r)) with b by (field; lra). reflexivity. }
  unfold H, circle_primitive, al, be.
  rewrite !sin_asin by assumption. rewrite !cos_asin by assumption.
  rewrite Sa, Sb. field. lra.
Qed.

Lemma is_RInt_2circle : forall a lo hi, 0 < a -> -a <= lo <= hi -> hi <= a ->
  is_RInt (fun x => 2 * sqrt (a * a - x * x)) lo hi
          (2 * (circle_primitive a hi - circle_primitive a lo)).
Proof.
  intros a lo hi Ha Hlo Hhi. apply is_RInt_scal_R. apply is_RInt_circle; lra.
Qed.

(** A circular segment is the area between its chord and its arc. *)
Lemma segment_area_nonneg : forall r d, 0 < r -> 0 <= d <= r -> 0 <= segment_area r d.
Proof.
  intros r d Hr Hd.
  assert (Hpos : (r - d) * 0 <= circle_primitive r r - circle_primitive r d <= (r - d) * r).
  { apply (is_RInt_bound (fun x => sqrt (r * r - x * x))); [lra | apply is_RInt_circle; lra|].
    intros x Hx. split; [apply sqrt_pos|]. apply sqrt_le_of_le_sq; nra. }
  replace (segment_area r d) with (2 * (circle_primitive r r - circle_primitive r d)).
  { lra. }
  assert (Hdr : -1 <= d / r <= 1).
  { split; [apply (Rmult_le_reg_r r); [lra|]; field_simplify; lra
           |apply (Rmult_le_reg_r r); [lra|]; field_simplify; lra]. }
  rewrite circle_primitive_edge by exact Hr.
  unfold segment_area, sector_area, triangle_area, circle_primitive. cbv zeta.
  rewrite acos_asin by exact Hdr. field; lra.
Qed.

(** ** Correctness: the overlap area is the integral of the slice lengths *)

Lemma slice_near : forall a s x, 0 <= s -> a * a - x * x <= s * s ->
  slice a s x = sqrt (a * a - x * x).
Proof.
  intros a s x Hs Hx. unfold slice. apply Rmin_right.
  apply sqrt_le_of_le_sq; assumption.
Qed.

Lemma slice_full : forall a s x, 0 <= s -> s * s <= a * a - x * x -> slice a s x = s.
Proof.
  intros a s x Hs Hx. unfold slice. apply Rmin_left.
  apply le_sqrt_of_sq_le; assumption.
Qed.

Lemma overlap_area_slices_nonneg : forall a s, 0 <= a -> 0 < s ->
  is_RInt (fun x => 2 * slice a s x) (-s) s (overlap_area a s).
Proof.
  intros a s Ha Hs.
  unfold overlap_area. cbv zeta. rewrite Rabs_pos_eq by exact Ha.
  destruct (Rle_dec s 0) as [Hs0|_]; [lra|].
  destruct (Rle_dec a s) as [Has|Has].
  - (* disc inside the square: integrate the full semicircle *)
    destruct (Req_dec a 0) as [Ha0|Ha0].
    + subst a. replace (PI * 0 * 0) with ((s - - s) * 0) by ring.
      apply (is_RInt_ext_le (fun _ => 0)); [lra| |apply is_RInt_const_R].
      intros x Hx. rewrite slice_far by nra. ring.
    + assert (Ha' : 0 < a) by lra.
      replace (PI * a * a) with
        ((- a - - s) * 0 + 2 * (circle_primitive a a - circle_primitive a (- a)) + (s - a) * 0).
      2:{ rewrite circle_primitive_opp, circle_primitive_edge by exact Ha'. field. }
      apply is_RInt_Chasles_R with a; [apply is_RInt_Chasles_R with (- a)|].
      * apply (is_RInt_ext_le (fun _ => 0)); [lra| |apply is_RInt_const_R].
        intros x Hx. rewrite slice_far by (lra || nra). ring.
      * apply (is_RInt_ext_le (fun x => 2 * sqrt (a * a - x * x))); [lra| |].
        -- intros x Hx. rewrite slice_near; [reflexivity|lra|nra].
        -- apply is_RInt_2circle; lra.
      * apply (is_RInt_ext_le (fun _ => 0)); [lra| |apply is_RInt_const_R].
        intros x Hx. rewrite slice_far by (lra || nra). ring.
  - destruct (Rle_dec a (s * sqrt 2)) as [Has2|Has2].
    + (* the four edges cut circular caps off the disc; the arc meets the edge
         x = ±s at height ±c, so slices are full for |x| <= c *)
      apply (le_s_sqrt2 a s Ha (Rlt_le _ _ Hs)) in Has2.
      set (c := sqrt (a * a - s * s)).
      assert (Hcc : c * c = a * a - s * s) by (apply sqrt_sqrt; nra).
      assert (Hc0 : 0 < c) by (apply sqrt_lt_R0; nra).
      assert (Hcs : c <= s) by nra.
      assert (Hca : c < a) by nra.
      assert (Hsa : s < a) by lra.
      replace (PI * a * a - 4 * segment_area a s) with
        (2 * (circle_primitive a (- c) - circle_primitive a (- s))
         + (c - - c) * (2 * s)
         + 2 * (circle_primitive a s - circle_primitive a c)).
      2:{ rewrite !circle_primitive_opp.
          unfold segment_area, sector_area, triangle_area, circle_primitive. cbv zeta.
          fold c.
          assert (Hu : 0 <= s / a <= 1).
          { split; [apply Rdiv_le_0_compat; lra|].
            apply (Rmult_le_reg_r a); [lra|]. field_simplify; lra. }
          assert (Hca' : c / a = sqrt (1 - (s / a)²)).
          { assert (E : sqrt (a * a - s * s) = a * sqrt (1 - (s / a)²)).
            { rewrite (sqrt_r2_minus a (s / a)) by (lra || (split; lra)).
              replace (a * (s / a)) with s by (field; lra). reflexivity. }
            unfold c. rewrite E. field. lra. }
          assert (Hac : sqrt (a * a - c * c) = s).
          { rewrite Hcc. replace (a * a - (a * a - s * s)) with (s * s) by ring.
            apply sqrt_square. lra. }
          rewrite Hac, Hca', asin_complement by exact Hu.
          rewrite acos_asin by lra. field. }
      apply is_RInt_Chasles_R with c; [apply is_RInt_Chasles_R with (- c)|].
      * apply (is_RInt_ext_le (fun x => 2 * sqrt (a * a - x * x))); [lra| |].
        -- intros x Hx. rewrite slice_near; [reflexivity|lra|nra].
        -- apply is_RInt_2circle; lra.
      * apply (is_RInt_ext_le (fun _ => 2 * s)); [lra| |apply is_RInt_const_R].
        intros x Hx. rewrite slice_full; [reflexivity|lra|nra].
      * apply (is_RInt_ext_le (fun x => 2 * sqrt (a * a - x * x))); [lra| |].
        -- intros x Hx. rewrite slice_near; [reflexivity|lra|nra].
        -- apply is_RInt_2circle; lra.
    + (* square inside the disc: every slice is full *)
      assert (Has2' : 2 * (s * s) < a * a).
      { destruct (Rle_lt_dec (a * a) (2 * (s * s))) as [H|H]; [|exact H].
        exfalso. apply Has2. apply le_s_sqrt2; lra. }
      replace (2 * s * (2 * s)) with ((s - - s) * (2 * s)) by ring.
      apply (is_RInt_ext_le (fun _ => 2 * s)); [lra| |apply is_RInt_const_R].
      intros x Hx. rewrite slice_full; [reflexivity|lra|nra].
Qed.

Lemma overlap_area_nonpos_side : forall r s, s <= 0 -> overlap_area r s = 0.
Proof.
  intros r s Hs. unfold overlap_area. cbv zeta.
  destruct (Rle_dec s 0); [reflexivity | lra].
Qed.

Lemma overlap_area_abs : forall r s, overlap_area (Rabs r) s = overlap_area r s.
Proof. intros r s. unfold overlap_area. cbv zeta. rewrite Rabs_Rabsolu. reflexivity. Qed.

Lemma Rabs_mult_self : forall r, Rabs r * Rabs r = r * r.
Proof. intro r. unfold Rabs. destruct (Rcase_abs r); ring. Qed.

(** Cavalieri: the area is the integral over x of the length of the slice. *)
Theorem overlap_area_slices : forall r s, 0 <= s ->
  is_RInt (fun x => 2 * slice r s x) (-s) s (overlap_area r s).
Proof.
  intros r s Hs. destruct (Req_dec s 0) as [Hs0|Hs0].
  - subst s. rewrite overlap_area_nonpos_side by lra. rewrite Ropp_0.
    apply (is_RInt_point (V := R_NormedModule)).
  - rewrite <- overlap_area_abs.
    apply (is_RInt_ext_le (fun x => 2 * slice (Rabs r) s x)); [lra| |].
    + intros x _. unfold slice. rewrite Rabs_mult_self. reflexivity.
    + apply overlap_area_slices_nonneg; [apply Rabs_pos | lra].
Qed.

(** ** Correctness: the overlap area is the double integral of the region *)

Definition in_overlap_dec (r s x y : R) :
  {in_overlap r s x y} + {~ in_overlap r s x y}.
Proof.
  unfold in_overlap, in_circle, in_square.
  destruct (Rle_dec (x * x + y * y) (r * r));
  destruct (Rle_dec (- s) x); destruct (Rle_dec x s);
  destruct (Rle_dec (- s) y); destruct (Rle_dec y s);
  first [left; tauto | right; tauto].
Defined.

(** Indicator function of the overlap region *)
Definition overlap_indicator (r s x y : R) : R :=
  if in_overlap_dec r s x y then 1 else 0.

(** Integrating the indicator along a vertical line gives the slice length. *)
Lemma inner_integral : forall r s x, 0 <= s -> -s <= x <= s ->
  is_RInt (fun y => overlap_indicator r s x y) (-s) s (2 * slice r s x).
Proof.
  intros r s x Hs Hx. unfold overlap_indicator.
  destruct (Rle_lt_dec (x * x) (r * r)) as [Hxr|Hxr].
  - set (m := slice r s x).
    assert (Hm : 0 <= m <= s) by (apply slice_bounds; exact Hs).
    replace (2 * m) with ((- m - - s) * 0 + (m - - m) * 1 + (s - m) * 0) by ring.
    apply is_RInt_Chasles_R with m; [apply is_RInt_Chasles_R with (- m)|].
    + apply (is_RInt_ext_le (fun _ => 0)); [lra| |apply is_RInt_const_R].
      intros y Hy. destruct (in_overlap_dec r s x y) as [Hin|]; [|reflexivity].
      apply (in_overlap_slice r s x y Hx Hxr) in Hin. fold m in Hin. lra.
    + apply (is_RInt_ext_le (fun _ => 1)); [lra| |apply is_RInt_const_R].
      intros y Hy. destruct (in_overlap_dec r s x y) as [|Hout]; [reflexivity|].
      exfalso. apply Hout. apply (in_overlap_slice r s x y Hx Hxr). fold m. lra.
    + apply (is_RInt_ext_le (fun _ => 0)); [lra| |apply is_RInt_const_R].
      intros y Hy. destruct (in_overlap_dec r s x y) as [Hin|]; [|reflexivity].
      apply (in_overlap_slice r s x y Hx Hxr) in Hin. fold m in Hin. lra.
  - rewrite slice_far by lra. replace (2 * 0) with ((s - - s) * 0) by ring.
    apply (is_RInt_ext_le (fun _ => 0)); [lra| |apply is_RInt_const_R].
    intros y Hy. destruct (in_overlap_dec r s x y) as [Hin|]; [|reflexivity].
    exfalso. exact (not_in_overlap_far r s x y Hxr Hin).
Qed.

(** Main theorem: [overlap_area r s] equals
    ∫_{-s}^{s} ∫_{-s}^{s} 1[(x, y) ∈ circle ∩ square] dy dx. *)
Theorem overlap_area_double_integral : forall r s, 0 <= s ->
  is_RInt (fun x => RInt (fun y => overlap_indicator r s x y) (-s) s) (-s) s
          (overlap_area r s).
Proof.
  intros r s Hs.
  apply (is_RInt_ext_le (fun x => 2 * slice r s x)); [lra| |apply overlap_area_slices, Hs].
  intros x Hx. symmetry. apply is_RInt_unique. apply inner_integral; lra.
Qed.

(** ** Correctness properties *)

Lemma overlap_area_ge_0 : forall r s, 0 <= overlap_area r s.
Proof.
  intros r s. destruct (Rle_lt_dec s 0) as [Hs|Hs].
  - rewrite overlap_area_nonpos_side by exact Hs. lra.
  - assert (H : (s - - s) * 0 <= overlap_area r s <= (s - - s) * (2 * s)).
    { apply (is_RInt_bound (fun x => 2 * slice r s x)); [lra | apply overlap_area_slices; lra|].
      intros x _. pose proof (slice_bounds r s x ltac:(lra)). lra. }
    lra.
Qed.

Lemma overlap_area_le_square : forall r s, 0 <= s -> overlap_area r s <= (2 * s) * (2 * s).
Proof.
  intros r s Hs.
  assert (H : (s - - s) * 0 <= overlap_area r s <= (s - - s) * (2 * s)).
  { apply (is_RInt_bound (fun x => 2 * slice r s x)); [lra | apply overlap_area_slices; lra|].
    intros x _. pose proof (slice_bounds r s x Hs). lra. }
  lra.
Qed.

Lemma overlap_area_le_circle : forall r s, overlap_area r s <= PI * r * r.
Proof.
  intros r s. pose proof PI_RGT_0 as Hpi. pose proof PI2_3_2 as Hpi3.
  replace (PI * r * r) with (PI * (Rabs r * Rabs r)) by (rewrite Rabs_mult_self; ring).
  pose proof (Rabs_pos r) as Ha.
  unfold overlap_area. cbv zeta. set (a := Rabs r) in *.
  destruct (Rle_dec s 0) as [Hs|Hs]; [nra|].
  destruct (Rle_dec a s) as [Has|Has]; [lra|].
  destruct (Rle_dec a (s * sqrt 2)) as [Has2|Has2].
  - pose proof (segment_area_nonneg a s ltac:(lra) ltac:(lra)). lra.
  - assert (Has2' : 2 * (s * s) < a * a).
    { destruct (Rle_lt_dec (a * a) (2 * (s * s))) as [H|H]; [|exact H].
      exfalso. apply Has2. apply le_s_sqrt2; lra. }
    nra.
Qed.

(** The overlap area is always non-negative *)
Lemma overlap_area_nonneg : forall R s,
  0 <= R -> 0 <= s -> 0 <= overlap_area R s.
Proof.
  intros R s _ _. apply overlap_area_ge_0.
Qed.

(** The overlap area is bounded by both the circle area and square area *)
Lemma overlap_area_bounded : forall R s,
  0 <= R -> 0 <= s ->
  overlap_area R s <= PI * R * R /\
  overlap_area R s <= (2 * s) * (2 * s).
Proof.
  intros R s _ Hs. split.
  - apply overlap_area_le_circle.
  - apply overlap_area_le_square. exact Hs.
Qed.

(** Symmetry: swapping x and y preserves overlap area (for square case) *)
Lemma overlap_area_symmetric : forall R s,
  overlap_area R s = overlap_area R s.
Proof.
  intros R s.
  reflexivity.
Qed.

(** The region itself is symmetric under swapping x and y. *)
Lemma in_overlap_swap : forall r s x y,
  in_overlap r s x y <-> in_overlap r s y x.
Proof.
  intros r s x y. unfold in_overlap, in_circle, in_square.
  split; intros [Hc [Hx Hy]]; repeat split; lra.
Qed.

(** ** Continuity *)

Ltac case_abs :=
  unfold Rabs in *;
  repeat match goal with
  | |- context [Rcase_abs ?x] => destruct (Rcase_abs x)
  | H : context [Rcase_abs ?x] |- _ => destruct (Rcase_abs x)
  end.

Lemma Rmin_lipschitz : forall s u v, Rabs (Rmin s u - Rmin s v) <= Rabs (u - v).
Proof.
  intros s u v. unfold Rmin.
  destruct (Rle_dec s u); destruct (Rle_dec s v);
    case_abs; lra.
Qed.

Lemma Rmax_lipschitz : forall u v, Rabs (Rmax u 0 - Rmax v 0) <= Rabs (u - v).
Proof.
  intros u v. unfold Rmax.
  destruct (Rle_dec u 0); destruct (Rle_dec v 0);
    case_abs; lra.
Qed.

Lemma sqrt_diff_le : forall u v, v <= u -> sqrt u - sqrt v <= sqrt (u - v).
Proof.
  intros u v Hvu. destruct (Rle_lt_dec v 0) as [Hv|Hv].
  - rewrite (sqrt_neg_0 v Hv). rewrite Rminus_0_r. apply sqrt_le_1_alt. lra.
  - pose proof (sqrt_sqrt u ltac:(lra)). pose proof (sqrt_sqrt v ltac:(lra)).
    pose proof (sqrt_sqrt (u - v) ltac:(lra)).
    pose proof (sqrt_pos v). pose proof (sqrt_pos (u - v)).
    assert (Hvu' : sqrt v <= sqrt u) by (apply sqrt_le_1_alt; lra).
    assert (Hsq : (sqrt u - sqrt v) * (sqrt u - sqrt v) <= sqrt (u - v) * sqrt (u - v))
      by nra.
    nra.
Qed.

(** √ is 1/2-Hölder continuous on the whole real line. *)
Lemma sqrt_holder : forall u v, Rabs (sqrt u - sqrt v) <= sqrt (Rabs (u - v)).
Proof.
  intros u v. destruct (Rle_dec v u) as [H|H].
  - assert (sqrt v <= sqrt u) by (apply sqrt_le_1_alt; exact H).
    rewrite !Rabs_pos_eq by lra. apply sqrt_diff_le. exact H.
  - assert (sqrt u <= sqrt v) by (apply sqrt_le_1_alt; lra).
    rewrite Rabs_minus_sym, (Rabs_minus_sym u v).
    rewrite !Rabs_pos_eq by lra. apply sqrt_diff_le. lra.
Qed.

Lemma slice_holder : forall r r' s x,
  Rabs (slice r s x - slice r' s x) <= sqrt (Rabs (r * r - r' * r')).
Proof.
  intros r r' s x. unfold slice.
  eapply Rle_trans; [apply Rmin_lipschitz|].
  eapply Rle_trans; [apply sqrt_holder|].
  replace (r * r - x * x - (r' * r' - x * x)) with (r * r - r' * r') by ring. lra.
Qed.

Lemma slice_mono_s : forall r s s' x, 0 <= s <= s' ->
  0 <= slice r s' x - slice r s x <= s' - s.
Proof.
  intros r s s' x Hs. unfold slice, Rmin.
  destruct (Rle_dec s' (sqrt (r * r - x * x))); destruct (Rle_dec s (sqrt (r * r - x * x)));
    lra.
Qed.

(** Changing the radius changes the area by at most 4s·√|r² - r'²|. *)
Lemma overlap_area_holder_r : forall r r' s, 0 <= s ->
  Rabs (overlap_area r s - overlap_area r' s) <= 4 * s * sqrt (Rabs (r * r - r' * r')).
Proof.
  intros r r' s Hs. set (K := sqrt (Rabs (r * r - r' * r'))).
  assert (HK : 0 <= K) by apply sqrt_pos.
  assert (H : (s - - s) * (- (2 * K)) <= overlap_area r s - overlap_area r' s
              <= (s - - s) * (2 * K)).
  { apply (is_RInt_bound (fun x => 2 * slice r s x - 2 * slice r' s x)); [lra| |].
    - apply is_RInt_minus_R; apply overlap_area_slices; exact Hs.
    - intros x _. pose proof (slice_holder r r' s x) as Hx. fold K in Hx.
      case_abs; lra. }
  apply Rabs_le. lra.
Qed.

(** Growing the square from s to s' adds at most 4(s'² - s²) of area. *)
Lemma overlap_area_lip_s : forall r s s', 0 <= s <= s' ->
  0 <= overlap_area r s' - overlap_area r s <= 4 * (s' - s) * (s' + s).
Proof.
  intros r s s' Hss.
  set (f' := fun x => 2 * slice r s' x).
  assert (H' : is_RInt f' (-s') s' (overlap_area r s'))
    by (apply overlap_area_slices; lra).
  assert (Hex : ex_RInt f' (-s') s') by (exists (overlap_area r s'); exact H').
  assert (Hex1 : ex_RInt f' (-s') (-s))
    by (apply (ex_RInt_Chasles_1 f' (-s') (-s) s'); [lra | exact Hex]).
  assert (Hex23 : ex_RInt f' (-s) s')
    by (apply (ex_RInt_Chasles_2 f' (-s') (-s) s'); [lra | exact Hex]).
  assert (Hex2 : ex_RInt f' (-s) s)
    by (apply (ex_RInt_Chasles_1 f' (-s) s s'); [lra | exact Hex23]).
  assert (Hex3 : ex_RInt f' s s')
    by (apply (ex_RInt_Chasles_2 f' (-s) s s'); [lra | exact Hex23]).
  set (l1 := RInt f' (-s') (-s)). set (l2 := RInt f' (-s) s). set (l3 := RInt f' s s').
  assert (H1 : is_RInt f' (-s') (-s) l1)
    by (apply (RInt_correct (V := R_CompleteNormedModule)); exact Hex1).
  assert (H2 : is_RInt f' (-s) s l2)
    by (apply (RInt_correct (V := R_CompleteNormedModule)); exact Hex2).
  assert (H3 : is_RInt f' s s' l3)
    by (apply (RInt_correct (V := R_CompleteNormedModule)); exact Hex3).
  assert (Hsum : overlap_area r s' = l1 + (l2 + l3)).
  { assert (E : is_RInt f' (-s') s' (l1 + (l2 + l3))).
    { apply is_RInt_Chasles_R with (-s); [exact H1|].
      apply is_RInt_Chasles_R with s; assumption. }
    transitivity (RInt f' (-s') s').
    - symmetry. apply is_RInt_unique. exact H'.
    - apply is_RInt_unique. exact E. }
  assert (B1 : (- s - - s') * 0 <= l1 <= (- s - - s') * (2 * s')).
  { apply (is_RInt_bound f'); [lra | exact H1 |].
    intros x _. unfold f'. pose proof (slice_bounds r s' x ltac:(lra)). lra. }
  assert (B3 : (s' - s) * 0 <= l3 <= (s' - s) * (2 * s')).
  { apply (is_RInt_bound f'); [lra | exact H3 |].
    intros x _. unfold f'. pose proof (slice_bounds r s' x ltac:(lra)). lra. }
  assert (B2 : (s - - s) * 0 <= l2 - overlap_area r s <= (s - - s) * (2 * (s' - s))).
  { apply (is_RInt_bound (fun x => f' x - 2 * slice r s x)); [lra | |].
    - apply is_RInt_minus_R; [exact H2 | apply overlap_area_slices; lra].
    - intros x _. unfold f'. pose proof (slice_mono_s r s s' x Hss). lra. }
  rewrite Hsum. split; nra.
Qed.

Lemma overlap_area_holder_s : forall r s s', 0 <= s -> 0 <= s' ->
  Rabs (overlap_area r s - overlap_area r s') <= 4 * Rabs (s - s') * (s + s').
Proof.
  intros r s s' Hs Hs'. destruct (Rle_dec s s') as [H|H].
  - pose proof (overlap_area_lip_s r s s' (conj Hs H)).
    rewrite Rabs_minus_sym, (Rabs_minus_sym s s').
    rewrite !Rabs_pos_eq by lra. lra.
  - apply Rnot_le_lt in H.
    pose proof (overlap_area_lip_s r s' s (conj Hs' (Rlt_le _ _ H))).
    rewrite !Rabs_pos_eq by lra. lra.
Qed.

Lemma overlap_area_clamp : forall r s, overlap_area r s = overlap_area r (Rmax s 0).
Proof.
  intros r s. destruct (Rle_dec s 0) as [H|H].
  - rewrite Rmax_right by exact H. rewrite !overlap_area_nonpos_side by lra. reflexivity.
  - rewrite Rmax_left by lra. reflexivity.
Qed.

(** Continuity: small changes in R or s produce small changes in overlap area *)
Theorem overlap_area_continuous : forall R s epsilon,
  0 < epsilon ->
  exists delta, 0 < delta /\
    forall R' s',
      Rabs (R - R') < delta ->
      Rabs (s - s') < delta ->
      Rabs (overlap_area R s - overlap_area R' s') < epsilon.
Proof.
  intros r s eps Heps.
  set (s0 := Rmax s 0).
  assert (Hs0 : 0 <= s0) by apply Rmax_r.
  set (K := 2 * Rabs r + 1).
  assert (HK : 0 < K) by (pose proof (Rabs_pos r); unfold K; lra).
  set (e1 := eps / (8 * (s0 + 1))).
  assert (He1' : e1 * (8 * (s0 + 1)) = eps) by (unfold e1; field; lra).
  assert (He1 : 0 < e1) by nra.
  set (d1 := e1 * e1 / K).
  assert (Hd1' : d1 * K = e1 * e1) by (unfold d1; field; lra).
  assert (Hd1 : 0 < d1) by nra.
  set (d2 := eps / (8 * (2 * s0 + 1))).
  assert (Hd2' : d2 * (8 * (2 * s0 + 1)) = eps) by (unfold d2; field; lra).
  assert (Hd2 : 0 < d2) by nra.
  exists (Rmin 1 (Rmin d1 d2)). split.
  { apply Rmin_glb_lt; [lra | apply Rmin_glb_lt; assumption]. }
  intros r' s' Hr Hs.
  assert (Hdl1 : Rmin 1 (Rmin d1 d2) <= 1) by apply Rmin_l.
  assert (Hdl2 : Rmin 1 (Rmin d1 d2) <= d1)
    by (eapply Rle_trans; [apply Rmin_r | apply Rmin_l]).
  assert (Hdl3 : Rmin 1 (Rmin d1 d2) <= d2)
    by (eapply Rle_trans; [apply Rmin_r | apply Rmin_r]).
  set (delta := Rmin 1 (Rmin d1 d2)) in *.
  set (t := Rmax s' 0).
  assert (Ht : 0 <= t) by apply Rmax_r.
  assert (Hst : Rabs (s0 - t) < delta)
    by (eapply Rle_lt_trans; [apply Rmax_lipschitz | exact Hs]).
  rewrite (overlap_area_clamp r s), (overlap_area_clamp r' s'). fold s0 t.
  (* vary the radius, then the square *)
  assert (HA : Rabs (overlap_area r s0 - overlap_area r' s0) <= eps / 2).
  { eapply Rle_trans; [apply overlap_area_holder_r; exact Hs0|].
    assert (Hrr : Rabs (r * r - r' * r') <= delta * K).
    { replace (r * r - r' * r') with ((r - r') * (r + r')) by ring.
      rewrite Rabs_mult.
      assert (Hsum : Rabs (r + r') <= K).
      { assert (Hr1 : Rabs (r - r') < 1) by lra. revert Hr1. unfold K, Rabs.
        destruct (Rcase_abs (r - r')); destruct (Rcase_abs (r + r'));
          destruct (Rcase_abs r); intro; lra. }
      apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | lra | exact Hsum]. }
    assert (Hsq : sqrt (Rabs (r * r - r' * r')) <= e1).
    { apply sqrt_le_of_le_sq; [lra|]. rewrite <- Hd1'.
      apply Rle_trans with (delta * K); [exact Hrr|].
      apply Rmult_le_compat_r; lra. }
    pose proof (sqrt_pos (Rabs (r * r - r' * r'))).
    nra. }
  assert (HB : Rabs (overlap_area r' s0 - overlap_area r' t) < eps / 2).
  { eapply Rle_lt_trans; [apply overlap_area_holder_s; assumption|].
    assert (Ht1 : t <= s0 + 1).
    { revert Hst. unfold Rabs. destruct (Rcase_abs (s0 - t)); intro; lra. }
    pose proof (Rabs_pos (s0 - t)).
    apply Rle_lt_trans with (4 * Rabs (s0 - t) * (2 * s0 + 1)).
    { apply Rmult_le_compat_l; lra. }
    nra. }
  replace (overlap_area r s0 - overlap_area r' t) with
    ((overlap_area r s0 - overlap_area r' s0) + (overlap_area r' s0 - overlap_area r' t))
    by ring.
  eapply Rle_lt_trans; [apply Rabs_triang|]. lra.
Qed.

(** ** Future work *)

(**
   TODO: Formalise the off-centre (position-dependent, 8-case) configuration
   TODO: Connect to numerical integration for validation
   TODO: Extract to Haskell for computational verification
*)
