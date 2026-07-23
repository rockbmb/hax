import Hax.core_models.core_models

attribute [specset bv, hax_bv_decide]
  core_models.convert.From._from

namespace core_models.num.Impl_8

@[spec]
def rotate_left (x : u32) (n : u32) : RustM u32 :=
  pure (UInt32.ofBitVec (BitVec.rotateLeft x.toBitVec n.toNat))

@[spec]
def from_le_bytes (x : RustArray u8 4) : RustM u32 :=
  pure (x.toVec[0].toUInt32
  + (x.toVec[1].toUInt32 <<< 8)
  + (x.toVec[2].toUInt32 <<< 16)
  + (x.toVec[3].toUInt32 <<< 24))

@[spec]
def to_le_bytes (x : u32) : RustM (RustArray u8 4) :=
  pure (.ofVec #v[
    (x % 256).toUInt8,
    (x >>> 8 % 256).toUInt8,
    (x >>> 16 % 256).toUInt8,
    (x >>> 24 % 256).toUInt8,
  ])

end core_models.num.Impl_8


attribute [spec] core_models.num.Impl_8.wrapping_add

open Std.Do
open Std.Tactic

namespace core_models.num.Impl_10

/-- `u128::checked_mul`. The generated core-models body is Rust-only (filtered in
    `core-models/hax.sh`); this handwritten definition supplies the Lean semantics:
    `Some (x * y)` when the product fits in `u128`, else `None`. -/
@[spec]
def checked_mul (x y : u128) : RustM (core_models.option.Option u128) := do
  let p : Nat := x.toNat * y.toNat
  if p < 2 ^ 128 then
    pure (core_models.option.Option.Some (UInt128.ofNat p))
  else
    pure core_models.option.Option.None

/-- `u128::checked_pow`. Rust computes this by exponentiation-by-squaring with
    per-step overflow checks; for `base ≥ 1` every intermediate is bounded by the
    final power, so overflow of any step implies overflow of `base ^ exp`, and the
    two formulations agree. `base = 0` returns `Some 0`/`Some 1` identically. -/
@[spec]
def checked_pow (base : u128) (exp : u32) : RustM (core_models.option.Option u128) := do
  let r : Nat := base.toNat ^ exp.toNat
  if r < 2 ^ 128 then
    pure (core_models.option.Option.Some (UInt128.ofNat r))
  else
    pure core_models.option.Option.None

@[spec]
theorem checked_mul_spec (x y : u128) :
    ⦃ ⌜ True ⌝ ⦄
    checked_mul x y
    ⦃ ⇓ r => ⌜
        (x.toNat * y.toNat < 2 ^ 128 ∧
          r = core_models.option.Option.Some (UInt128.ofNat (x.toNat * y.toNat))) ∨
        (x.toNat * y.toNat ≥ 2 ^ 128 ∧ r = core_models.option.Option.None) ⌝ ⦄ := by
  unfold checked_mul
  mvcgen
  · left; exact And.intro (by assumption) rfl
  · omega

@[spec]
theorem checked_pow_spec (base : u128) (exp : u32) :
    ⦃ ⌜ True ⌝ ⦄
    checked_pow base exp
    ⦃ ⇓ r => ⌜
        (base.toNat ^ exp.toNat < 2 ^ 128 ∧
          r = core_models.option.Option.Some (UInt128.ofNat (base.toNat ^ exp.toNat))) ∨
        (base.toNat ^ exp.toNat ≥ 2 ^ 128 ∧ r = core_models.option.Option.None) ⌝ ⦄ := by
  unfold checked_pow
  mvcgen
  · left; exact And.intro (by assumption) rfl
  · omega

end core_models.num.Impl_10
