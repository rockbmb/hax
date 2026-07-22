---
weight: 1
---

# Proving properties

In the previous chapter, we proved one property of the `square` function:
panic freedom.

This contract stipulates that, given a small input, the function will
_return a value_: it will not panic or diverge. We could enrich the
contract of `square` with a post-condition about the fact it is an
increasing function:
```{.rust .playable .lean-backend}
#[hax_lib::requires(x < 16)]
#[hax_lib::ensures(|res| res >= x)]
pub fn square(x: u8) -> u8 {
    x * x
}
```

Reextract:
```
cargo hax into lean
```

We will have to adjust the proof a little to make it work:
```
@[spec]
theorem square.spec.proof (x : Std.U8) : square.spec x := by
  unfold square.spec square
  hax_mvcgen <;> grind [Nat.le_mul_self]
```

Rerun `lake build` to verify the proof.

## See more examples
The property that we prove above demonstrates a very simple case of a proof using hax and Lean. For a more complex example, have a look at the
[`examples`](https://github.com/cryspen/hax/tree/main/examples) 
section of hax. 


