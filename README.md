# Secret-U: A lazily-evaluated set of Rust types for offloadable, constant-time computation

This is a bit of exploratory work into what a lazily-evaluated, offloadable,
constant-time type-system might look like in Rust.

The primary goal is to be able to perform secrecy-preserving cryptographic
computation in constant-time, even when running in a sandboxed environment with
little control over the native execution.

There are several methods to go about solving this problem, such as extending
the sandbox itself to support constant-time instructions ([CT-Wasm]), or
providing host calls for each constant-time operation (which sounds very
expensive). The method explored here is to provide a separate execution engine
specifically for performing constant-time computation, much like a coprocessor.

Quick definitions of all these adjectives:

- constant-time - In cryptographic algorithms, constant-time is a property that
  implies a given computation takes the same amount of time to execute
  independent of the data being computed. This is important for
  secrecy-preserving computation, as otherwise an algorithm would be susceptible
  to timing attacks. Where information about a secret can be extracted by
  timing how long a given computation takes.

- constant-time type-system - We can statically determine that an algorithm is
  constant-time by leveraging a type-system, tagging data as secrecy-preserving,
  and rejecting any operations that violated constant-time constraints.

  Since most code eventually needs to actually do something with this data, most
  constant-time type-systems include a "declassify" operation to move data out
  of secrecy-preserving types. Much like Rust's unsafe keyword, declassify acts
  as a flag indicating where secrecy-preserving operations stop.

- lazily-evaluated - Rather than dispatch a host call for each constant-time
  operation, the secret-u integers internally build an AST, which doesn't get
  executed until a declassify is called.

  A fascinating side-effect of limiting side-effects until declassify means that
  constant-time operations are perfect targets for lazy evaluation.

- offloadable - As an experiment, secret-u is intended to run in sandboxes
  where the application may not have enough control of the native execution to
  ensure that operations are constant-time. As an alternative, secret-u compiles
  down into its own bytecode, which can be executed by a separate, constant-time
  preserving engine outside of the sandbox.

  This bytecode contains only constant-time operations, which offers its own
  litmus test for constant-time algorithms. If an algorithm can compile for it,
  it must be constant-time. As a side-effect of only supporting constant-time
  operations, there is no loops or branches, which simplifies the engine quite
  a bit. Perhaps humorously, this also means the engine is not Turing-complete,
  and categorically only a finite-state machine.

  Another nice side-effect, is that any intermediary results are implicitly
  isolated from the original sandbox.

## How it works

Secret-U has multiple layers:

```
Secret types -> AST -> Bytecode -> Execution
```

For an arbitrary example, consider a binary-search based,
constant-time, 4-bit square-root:

``` rust
fn sqrt(x: u32) -> u32 {
    // binary search
    let mut lo = 0;
    let mut hi = x;

    // each round determines one bit, so only need log(x) rounds
    for _ in 0..8 {
        // test mid
        let mid = (lo + hi) >> 1;
        let mid_sq = mid*mid;

        // find new lo/hi
        if mid_sq < x {
            lo = mid;
        } else {
            hi = mid;
        }
    }

    // lo and hi should converge
    hi
}
```

This can be rewritten using secret-u integers to type-check for
constant-time. Note that we need to tweak the implementation a bit
to work with secret-u integers.

1. secret-u integers are not Copy, so clone must be called occasionally,
   however much like Rc, this is a cheap operation that internally increments
   a reference count.

2. The `if` statement is not constant-time, so will fail to compile. Instead
   we use secret-u's `select` method to conditionally select a value. Note this
   eagerly evaluates both branches.

3. In Rust, Eq can't be overridden to return a different type, so we need to
   use secret-u's `eq` method to compare secret-u integers.

4. We also need to use either `SecretU32::new` or `SecretU32::const_` to create
   secret-u integers. The difference is that secret-u integer's created with
   `SecretU32::new` are secrecy-preserving, whereas secret-u integer's created
   with `SecretU32::const_` are susceptible to compile-time optimizations.

``` rust
#[lazy_compile]
fn sqrt(x: SecretU32) -> SecretU32 {
    // binary search
    let mut lo = SecretU32::const_(0);
    let mut hi = x.clone();

    // each round determines one bit, so only need log(x) rounds
    for _ in 0..8 {
        // test mid
        let mid = (lo.clone() + hi.clone()) >> SecretU32::const_(1);
        let mid_sq = mid.clone()*mid.clone();

        // find new lo/hi using select to preserve const-time
        let mid_sq_lt = mid_sq.lt(x.clone());
        lo = mid_sq_lt.clone().select(mid.clone(), lo.clone());
        hi = mid_sq_lt.clone().select(hi.clone(), mid.clone());
    }

    // lo and hi should converge
    hi
}
```

If we compile and run the code with `--features debug-ast` enabled we can
view the generated AST:

```
tree:
    a = (u32.sym "x")
    b = (u32.shr_u a (u32.const 0x00000001))
    c = (u32.lt_u (u32.mul b b) a)
    d = (u32.select c b (u32.const 0x00000000))
    e = (u32.select c a b)
    f = (u32.shr_u (u32.add d e) (u32.const 0x00000001))
    g = (u32.lt_u (u32.mul f f) a)
    h = (u32.select g f d)
    i = (u32.select g e f)
    j = (u32.shr_u (u32.add h i) (u32.const 0x00000001))
    k = (u32.lt_u (u32.mul j j) a)
    l = (u32.select k j h)
    m = (u32.select k i j)
    n = (u32.shr_u (u32.add l m) (u32.const 0x00000001))
    o = (u32.lt_u (u32.mul n n) a)
    p = (u32.select o n l)
    q = (u32.select o m n)
    r = (u32.shr_u (u32.add p q) (u32.const 0x00000001))
    s = (u32.lt_u (u32.mul r r) a)
    t = (u32.select s r p)
    u = (u32.select s q r)
    v = (u32.shr_u (u32.add t u) (u32.const 0x00000001))
    w = (u32.lt_u (u32.mul v v) a)
    x = (u32.select w v t)
    y = (u32.select w u v)
    z = (u32.shr_u (u32.add x y) (u32.const 0x00000001))
    a2 = (u32.lt_u (u32.mul z z) a)
    b2 = (u32.select a2 y z)
    c2 = (u32.shr_u (u32.add (u32.select a2 z x) b2) (u32.const 0x00000001))
    (u32.select (u32.lt_u (u32.mul c2 c2) a) b2 c2)
```

With `--features debug-bytecode`, we can view the generated bytecode:

```
state:
    00 00 00 00 cc cc cc cc 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
bytecode:
    2001000100010000 u32.arg s4, s4
    2040000200010001 u32.shr_u s8, s4, 0x0001
    2033000300020002 u32.mul s12, s8, s8
    2011000300030001 u32.lt_u s12, s12, s4
    2006000400030000 u32.move s16, s12
    200b000400010002 u32.select s16, s4, s8
    2207000500000000 u8x4.splat s20, 0x00
    200b000300020005 u32.select s12, s8, s20
    202f000500030004 u32.add s20, s12, s16
    2040000500050001 u32.shr_u s20, s20, 0x0001
    2033000200050005 u32.mul s8, s20, s20
    2011000200020001 u32.lt_u s8, s8, s4
    2006000600020000 u32.move s24, s8
    200b000600040005 u32.select s24, s16, s20
    200b000200050003 u32.select s8, s20, s12
    202f000300020006 u32.add s12, s8, s24
    2040000300030001 u32.shr_u s12, s12, 0x0001
    2033000400030003 u32.mul s16, s12, s12
    2011000400040001 u32.lt_u s16, s16, s4
    2006000500040000 u32.move s20, s16
    200b000500060003 u32.select s20, s24, s12
    200b000400030002 u32.select s16, s12, s8
    202f000600040005 u32.add s24, s16, s20
    2040000600060001 u32.shr_u s24, s24, 0x0001
    2033000200060006 u32.mul s8, s24, s24
    2011000200020001 u32.lt_u s8, s8, s4
    2006000300020000 u32.move s12, s8
    200b000300050006 u32.select s12, s20, s24
    200b000200060004 u32.select s8, s24, s16
    202f000600020003 u32.add s24, s8, s12
    2040000600060001 u32.shr_u s24, s24, 0x0001
    2033000400060006 u32.mul s16, s24, s24
    2011000400040001 u32.lt_u s16, s16, s4
    2006000500040000 u32.move s20, s16
    200b000500030006 u32.select s20, s12, s24
    200b000400060002 u32.select s16, s24, s8
    202f000600040005 u32.add s24, s16, s20
    2040000600060001 u32.shr_u s24, s24, 0x0001
    2033000200060006 u32.mul s8, s24, s24
    2011000200020001 u32.lt_u s8, s8, s4
    2006000300020000 u32.move s12, s8
    200b000300050006 u32.select s12, s20, s24
    200b000200060004 u32.select s8, s24, s16
    202f000600020003 u32.add s24, s8, s12
    2040000600060001 u32.shr_u s24, s24, 0x0001
    2033000400060006 u32.mul s16, s24, s24
    2011000400040001 u32.lt_u s16, s16, s4
    2006000500040000 u32.move s20, s16
    200b000500030006 u32.select s20, s12, s24
    200b000400060002 u32.select s16, s24, s8
    202f000600040005 u32.add s24, s16, s20
    2040000600060001 u32.shr_u s24, s24, 0x0001
    2033000400060006 u32.mul s16, s24, s24
    2011000400040001 u32.lt_u s16, s16, s4
    200b000400050006 u32.select s16, s20, s24
    2002000000040000 u32.ret s0, s16
```

Lets say with call `sqrt` with `sqrt(16)`. With `--features debug-trace` we
can view a trace of the execution. Note that due to us printing all
intermediary values directly to standard out, this is obviously not
secrecy-preserving:

```
trace:
    u32.arg s4, s4               : 00 00 00 00 10 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
    u32.shr_u s8, s4, 0x0001     : 00 00 00 00 10 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
    u32.mul s12, s8, s8          : 00 00 00 00 10 00 00 00 08 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
    u32.lt_u s12, s12, s4        : 00 00 00 00 10 00 00 00 08 00 00 00 40 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
    u32.move s16, s12            : 00 00 00 00 10 00 00 00 08 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
    u32.select s16, s4, s8       : 00 00 00 00 10 00 00 00 08 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
    u8x4.splat s20               : 00 00 00 00 10 00 00 00 08 00 00 00 00 00 00 00 08 00 00 00 00 00 00 00 00 00 00 00
    u32.select s12, s8, s20      : 00 00 00 00 10 00 00 00 08 00 00 00 00 00 00 00 08 00 00 00 00 00 00 00 00 00 00 00
    u32.add s20, s12, s16        : 00 00 00 00 10 00 00 00 08 00 00 00 00 00 00 00 08 00 00 00 00 00 00 00 00 00 00 00
    u32.shr_u s20, s20, 0x0001   : 00 00 00 00 10 00 00 00 08 00 00 00 00 00 00 00 08 00 00 00 08 00 00 00 00 00 00 00
    u32.mul s8, s20, s20         : 00 00 00 00 10 00 00 00 08 00 00 00 00 00 00 00 08 00 00 00 04 00 00 00 00 00 00 00
    u32.lt_u s8, s8, s4          : 00 00 00 00 10 00 00 00 10 00 00 00 00 00 00 00 08 00 00 00 04 00 00 00 00 00 00 00
    u32.move s24, s8             : 00 00 00 00 10 00 00 00 00 00 00 00 00 00 00 00 08 00 00 00 04 00 00 00 00 00 00 00
    u32.select s24, s16, s20     : 00 00 00 00 10 00 00 00 00 00 00 00 00 00 00 00 08 00 00 00 04 00 00 00 00 00 00 00
    u32.select s8, s20, s12      : 00 00 00 00 10 00 00 00 00 00 00 00 00 00 00 00 08 00 00 00 04 00 00 00 04 00 00 00
    u32.add s12, s8, s24         : 00 00 00 00 10 00 00 00 00 00 00 00 00 00 00 00 08 00 00 00 04 00 00 00 04 00 00 00
    u32.shr_u s12, s12, 0x0001   : 00 00 00 00 10 00 00 00 00 00 00 00 04 00 00 00 08 00 00 00 04 00 00 00 04 00 00 00
    u32.mul s16, s12, s12        : 00 00 00 00 10 00 00 00 00 00 00 00 02 00 00 00 08 00 00 00 04 00 00 00 04 00 00 00
    u32.lt_u s16, s16, s4        : 00 00 00 00 10 00 00 00 00 00 00 00 02 00 00 00 04 00 00 00 04 00 00 00 04 00 00 00
    u32.move s20, s16            : 00 00 00 00 10 00 00 00 00 00 00 00 02 00 00 00 ff ff ff ff 04 00 00 00 04 00 00 00
    u32.select s20, s24, s12     : 00 00 00 00 10 00 00 00 00 00 00 00 02 00 00 00 ff ff ff ff ff ff ff ff 04 00 00 00
    u32.select s16, s12, s8      : 00 00 00 00 10 00 00 00 00 00 00 00 02 00 00 00 ff ff ff ff 04 00 00 00 04 00 00 00
    u32.add s24, s16, s20        : 00 00 00 00 10 00 00 00 00 00 00 00 02 00 00 00 02 00 00 00 04 00 00 00 04 00 00 00
    u32.shr_u s24, s24, 0x0001   : 00 00 00 00 10 00 00 00 00 00 00 00 02 00 00 00 02 00 00 00 04 00 00 00 06 00 00 00
    u32.mul s8, s24, s24         : 00 00 00 00 10 00 00 00 00 00 00 00 02 00 00 00 02 00 00 00 04 00 00 00 03 00 00 00
    u32.lt_u s8, s8, s4          : 00 00 00 00 10 00 00 00 09 00 00 00 02 00 00 00 02 00 00 00 04 00 00 00 03 00 00 00
    u32.move s12, s8             : 00 00 00 00 10 00 00 00 ff ff ff ff 02 00 00 00 02 00 00 00 04 00 00 00 03 00 00 00
    u32.select s12, s20, s24     : 00 00 00 00 10 00 00 00 ff ff ff ff ff ff ff ff 02 00 00 00 04 00 00 00 03 00 00 00
    u32.select s8, s24, s16      : 00 00 00 00 10 00 00 00 ff ff ff ff 04 00 00 00 02 00 00 00 04 00 00 00 03 00 00 00
    u32.add s24, s8, s12         : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 02 00 00 00 04 00 00 00 03 00 00 00
    u32.shr_u s24, s24, 0x0001   : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 02 00 00 00 04 00 00 00 07 00 00 00
    u32.mul s16, s24, s24        : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 02 00 00 00 04 00 00 00 03 00 00 00
    u32.lt_u s16, s16, s4        : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 09 00 00 00 04 00 00 00 03 00 00 00
    u32.move s20, s16            : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 ff ff ff ff 04 00 00 00 03 00 00 00
    u32.select s20, s12, s24     : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 ff ff ff ff ff ff ff ff 03 00 00 00
    u32.select s16, s24, s8      : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 ff ff ff ff 04 00 00 00 03 00 00 00
    u32.add s24, s16, s20        : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 03 00 00 00 04 00 00 00 03 00 00 00
    u32.shr_u s24, s24, 0x0001   : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 03 00 00 00 04 00 00 00 07 00 00 00
    u32.mul s8, s24, s24         : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 03 00 00 00 04 00 00 00 03 00 00 00
    u32.lt_u s8, s8, s4          : 00 00 00 00 10 00 00 00 09 00 00 00 04 00 00 00 03 00 00 00 04 00 00 00 03 00 00 00
    u32.move s12, s8             : 00 00 00 00 10 00 00 00 ff ff ff ff 04 00 00 00 03 00 00 00 04 00 00 00 03 00 00 00
    u32.select s12, s20, s24     : 00 00 00 00 10 00 00 00 ff ff ff ff ff ff ff ff 03 00 00 00 04 00 00 00 03 00 00 00
    u32.select s8, s24, s16      : 00 00 00 00 10 00 00 00 ff ff ff ff 04 00 00 00 03 00 00 00 04 00 00 00 03 00 00 00
    u32.add s24, s8, s12         : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 03 00 00 00 04 00 00 00 03 00 00 00
    u32.shr_u s24, s24, 0x0001   : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 03 00 00 00 04 00 00 00 07 00 00 00
    u32.mul s16, s24, s24        : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 03 00 00 00 04 00 00 00 03 00 00 00
    u32.lt_u s16, s16, s4        : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 09 00 00 00 04 00 00 00 03 00 00 00
    u32.move s20, s16            : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 ff ff ff ff 04 00 00 00 03 00 00 00
    u32.select s20, s12, s24     : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 ff ff ff ff ff ff ff ff 03 00 00 00
    u32.select s16, s24, s8      : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 ff ff ff ff 04 00 00 00 03 00 00 00
    u32.add s24, s16, s20        : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 03 00 00 00 04 00 00 00 03 00 00 00
    u32.shr_u s24, s24, 0x0001   : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 03 00 00 00 04 00 00 00 07 00 00 00
    u32.mul s16, s24, s24        : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 03 00 00 00 04 00 00 00 03 00 00 00
    u32.lt_u s16, s16, s4        : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 09 00 00 00 04 00 00 00 03 00 00 00
    u32.select s16, s20, s24     : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 ff ff ff ff 04 00 00 00 03 00 00 00
    u32.ret s0, s16              : 00 00 00 00 10 00 00 00 03 00 00 00 04 00 00 00 04 00 00 00 04 00 00 00 03 00 00 00
result:
    0x00000004
```

## Other features

secret-u has a number of other experiments tossed into this experimental salad:

- Big integers

  secret-u supports powers-of-two integers up to SecretU512. This provides an
  interesting alternative to dynamically-sized bigint libraries, while avoiding
  secrecy-leaking pitfalls caused by value-dependent bigint sizes.

  ``` rust
  (SecretU512::one() + SecretU512::one()).declassify_le_bytes() => [
    2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  ]
  ```

- SIMD integers

  It turns out SIMD operations share a lot of the limitations of constant-time
  operations, and leveraging SIMD can often improve an algorithm's performance.
  In addition to Rust's normal integer types, secret-u includes a set of SIMD
  types that mirror the types available in [packed_simd].

  ``` rust
  (SecretU16x8::new_splat(1) + SecretU16x8::new_splat(1)).declassify_lanes() => (
      2,
      2,
      2,
      2,
      2,
      2,
      2,
      2,
  )
  ```

  A somewhat interesting side-effect in secret-u is that even if SIMD hardware
  isn't available, SIMD may still improve performance in the execution engine
  due to having to decode fewer bytecode instructions.

- Compiled bytecode

  secret-u can compile functions into bytecode using either the `compile!`
  macro or `#[lazy_compile]` attribute. This is useful for performance sensitive
  code that calls a secret-u function in a tight loop, such as most hash or
  encryption schemes.

  `compile!` works by introducing symbolic AST nodes, executing the provided
  function, and then compiling the resulting AST into bytecode.

  `#[lazy_compile]` creates a function that internally calls `compile!` on the
  first invocation.

  It's worth noting that there is no option to compile bytecode at Rust's
  compile-time. While this is theoretical possible, there's currently no way
  to evaluate Rust code in a proc_macro, making possible solutions incredibly
  complicated (reimplement a Rust parser? call `rustc` externally? I feel like
  these are all bad ideas).

- Bitsliced and shuffle-based tables

  A side-effect of secret-u integers is that they can't be used for array
  indices. This is intentional as array lookups fail to be constant-time due
  to cache timings.

  As an alternative, two attributes are provided for converting lookup tables
  into either a bitslice or shuffle-based representation.

  `#[bitslice_table]` converts a lookup table into its bitsliced representation.
  This is where each bit is evaluated as a boolean expression that has been
  minified thanks to the [boolean_expression] crate.

  Note that boolean miniziation is an NP-Hard problem, so the result is only
  a heuristically minified set of expressions.

  For example, this:

  ``` rust
  #[bitslice_table]
  const table: [u8; 4] = [4, 3, 2, 1];
  ```

  Compiles into this:

  ``` rust
  fn table(a: SecretU8) -> SecretU8 {
      let mut a: [SecretU8; 2usize] = [a, SecretU8::zero()];
      let mut dim = 1usize;
      let mut mask = 1;
      while dim > 0 {
          let dim_s = SecretU8::const_(dim as u8);
          let mask_s = SecretU8::const_(mask);
          let mut i = 0;
          while i < 2usize {
              let x = mask_s.clone() & ((a[i].clone() >> dim_s.clone()) ^ a[i+dim].clone());
              a[i] ^= x.clone() << dim_s.clone();
              a[i+dim] ^= x;
              i = (i+dim+1) & !dim;
          }
          dim /= 2;
          mask ^= mask << dim;
      }
      let mut b: [SecretU8; 4usize] = [
          ((a[1].clone() & a[0].clone()) | ((!a[1].clone()) & a[0].clone())),
          ((a[1].clone() & (!a[0].clone())) | ((!a[1].clone()) & a[0].clone())),
          (((!a[1].clone()) & (!a[0].clone())) | SecretU8::zero()),
          SecretU8::zero()
      ]
      let mut dim = 2usize;
      let mut mask = 3;
      while dim > 0 {
          let dim_s = SecretU8::const_(dim as u8);
          let mask_s = SecretU8::const_(mask);
          let mut i = 0;
          while i < 4usize {
              let x = mask_s.clone() & ((b[i].clone() >> dim_s.clone()) ^ b[i+dim].clone());
              b[i] ^= x.clone() << dim_s.clone();
              b[i+dim] ^= x;
              i = (i+dim+1) & !dim;
          }
          dim /= 2;
          mask ^= mask << dim;
      }
      (SecretU8::const_(15) & b[0].clone())
  }
  ```

  `#[shuffle_table]`, on the other hand, converts a lookup table into a
  shuffle-based representation. This is effectively a brute-force tree of
  comparisons, however leverages SIMD shuffle instructions to significantly
  reduce the leaves of the tree.

  Note that the performance of `#[shuffle_table]` depends heavily on what
  hardware is available. With no SIMD shuffle instructions, the lookup will
  take O(number of elements) `select` operations. With, for example, Arm Neon's
  2x16-byte `tbl` instruction, only 8 `shuffles` and 7 `selects` are needed.

  For example, this:

  ``` rust
  #[shuffle_table]
  const table: [u8; 4] = [4, 3, 2, 1];
  ```

  Compiles into this:

  ``` rust
  fn table(a: SecretU8) -> SecretU8 {
      let a0 = SecretU8x2::cast(
          SecretU16::from(
              SecretU8::cast(
                  SecretU8::cast(a.clone() & SecretU8::const_(127))
              )
          )
      );
      let b = a0.clone().shuffle(
          SecretU8x2::const_slice(&[4, 3]),
          SecretU8x2::const_slice(&[2, 1])
      );
      let b = SecretU8::cast(
          SecretU8::cast(
              SecretU16::cast(b)
          )
      );
      b
  }
  ```

  If these approaches both seem expensive, that's because they are. However!
  these can both be easily parallelized, allowing multiple lookups to occur
  simultaneously, significantly reducing the performance impact.

  ``` rust
  #[bitslice_table(parallel=32)]
  const table: [u8; 4] = [4, 3, 2, 1];
  ```

  ``` rust
  fn table(a: SecretU8x32) -> SecretU8x32 {
      blablabla
  }
  ```

## Quirks

- Rust has very strict requirements for the Copy trait, the type must be
  byte-copyable. Since secret-u falls back to reference counting, it can't
  implement Copy. Much like Rc, this requires explicit calls to clone.

  The clones are still relatively cheap, but unfortunately this does add
  quite a bit of syntax noise.

- Rust's Eq and Ord are strictly defined to return `bool`. Unfortunately we
  can't return a non-secret `bool`, as this would leak secret information.
  Instead we define our own `secret_u::traits::Eq` and `secret_u::traits::Ord`
  which are defined to return SecretBool.

  The most annoying side effect is not being able to use comparison operators,
  instead relying on eq/ne/lt/etc methods.

- secret-u does not support division. From what I can tell, division is missing
  from both all constant-time type-systems and all SIMD instructions sets.

- Declassify reduces an AST into bytecode, which means you can't use declassify
  in a `compile!` function. This has the oddly beneficial side effect that
  `compile!` functions are entirely secrecy-preserving.

- A downside of this declassify limitation is that declassify is internally used
  to pass secrets into the execution engine. This means that you can't call
  `compile!` functions nested inside `compile!` functions. You can however keep
  `compile!` and non-`compile!` copies around for this purpose.

  In theory it could be possible for secret-u to nest `compile!` functions, by
  keeping the AST around and patching symbols at compile time, but this has not
  been explored due to the complexity it would bring.

- `compile!` functions redefine their arguments to take references. This is to
  internally avoid extra clone->compile->exec loops due to cloning arguments.

- Due to the limits of the constant-time bytecode, all loops are implicitly
  unrolled. This may or may not be faster, and can have some odd side-effects
  such as extra memory usage.

- secret-u is not thread-safe, at all. It probably could be, but no effort
  was put into it. Of course Rust will compile with an error if thread-safety
  is violated.

- There are a number of redundant instructions, this makes the compiler
  simpler, but may eventually lead to more opcode pressure.

  These instructions are completely redundant, but are present for symmetry,
  making the compiler simpler in a number of places:

  - gt_u r0, r1, r2 => lt_u r0, r2, r1
  - gt_s r0, r1, r2 => lt_s r0, r2, r1
  - ge_u r0, r1, r2 => le_u r0, r2, r1
  - ge_s r0, r1, r2 => le_s r0, r2, r1
  - sub_c r0, r1, imm => add_c r0, r1, -imm
  - andnot_c r0, r1, imm => and_c r0, r1, !imm

  Additionally, a couple unops _could_ be replaced by binops with immediates,
  but because of the extra decoding, these would be slower

  - not r0, r1 => xor r0, r1, -1
  - neg r0, r1 => mul r0, r1, -1

## Examples

See the examples in the examples folder for some examples:

- [sha256_reference](examples/sha256_reference.rs) - A non-constant-time
  reference implementation of SHA256, based on:

  - https://github.com/B-Con/crypto-algorithms

- [sha256](examples/sha256.rs) - A naive implementation of SHA256 using
  secret-u types.

- [sha256_fast](examples/sha256_fast.rs) - A faster SHA256 implementation
  using secret-u's compile macro to compile the computation down to the
  constant-time bytecode once.

- [aes_reference](examples/aes_reference.rs) - A non-constant-time reference
  implementation of AES, based on:

  - https://github.com/B-Con/crypto-algorithms
  - https://github.com/kokke/tiny-AES-c

- [aes](examples/aes.rs) - An implementation of AES CTR mode using
  secret-u types.

- [aes_more_simd](examples/aes_more_simd.rs) - A version of AES that operates
  on 64-byte blocks instead of 16-byte blocks, using SIMD to encrypt multiple
  16-byte blocks in parallel.

- [chacha20_reference](examples/chacha20_reference.rs) - A non-constant-time
  reference implementation of ChaCha20, based on:

  - https://cr.yp.to/chacha.html

- [chacha20](examples/chacha20.rs) - An implementation of ChaCha20 using
  secret-u types.

- [chacha20_simd](examples/chacha20_simd.rs) - An implementation of ChaCha20
  that leverages SIMD instructions to operate on u32x4 rows simultaneously.

- [sss](examples/sss.rs) - An implementation of Shamir's secret sharing
  scheme in GF(256), this makes heavy use of secret-u's bitslice_table and
  shuffle_table attributes to compile lookup tables into their constant-time
  friendly representations.

- [sss_simd](examples/sss_simd.rs) - An implementation of Shamir's secret
  sharing scheme in GF(256) which extends the sss example with SIMD operations
  to perform the computation in parallel.

## Testing

Tests and examples can be tested with the Makefile

``` bash
$ make test
```

## Benchmarking

There's not much benchmarking at the moment, there is only a prototype
interpreter in pure Rust that isn't gauranteed to execute in constant-time,
so benchmark results would not be the most useful.

However we can measure the runtime of the example code:

``` bash
$ make bench-sha256
```

On my machine:
```
sha256_reference  0m0.017s
sha256            0m19.304s
sha256_fast       0m0.110s
```

`sha256_reference` provides a native, non-constant-time sha256 implementation,
so we can expect it to be the fastest. `sha256` naively recompiles the bytecode
during every iteration, while `sha256_fast` uses `compile!` to avoid
recompilation.

``` bash
$ make bench-aes
```

On my machine:
```
aes_reference           0m0.033s
aes_shuffle             0m3.091s
aes_bitslice            0m14.105s
aes_more_simd_shuffle   0m1.649s
aes_more_simd_bitslice  0m5.679s
```

`aes_reference` again is not constant-time, and native, so it being the fastest
is not surprising. The `aes_more_simd_*` versions operate on 64-byte blocks in
parallel, instead of 16-byte blocks, and we see a proportional performance
increase.

``` bash
$ make bench-chacha20
```

On my machine:
```
chacha20_reference  0m0.023s
chacha20            0m0.077s
chacha20_simd       0m0.071s
```

chacha20 is both constant-time friendly and remarkably parallelizable,
which shows in its performance.

``` bash
$ make bench-sss
```

On my machine:
```
sss_shuffle        0m0.005s
sss_simd_shuffle   0m0.001s
sss_bitslice       0m0.041s
sss_simd_bitslice  0m0.020s
```

This byte-wise implementation of Shamir's secret sharing is immensely
parallelizable, unfortunately with a test size of dozens of bytes this
benchmark is mostly catching setup+compilation costs. Still interesting
to note that the SIMD version has increased performance.

This example is less interesting for benchmarking, more interesting for
the issues it causes the Rust compiler (oom, stack overflow, etc) due to the
large expressions the 510-byte bitsliced-table creates.


## Prior art

- [secret_integers] - A set of Rust types that ensures operations are limited
  to constant-time operations.

- [CT-Wasm] - A constant-time type-system extension to WebAssembly

- [FaCT] - A constant-time programming language for verifying constant-time
  properties at compile-time

## Possible future work

- Implement the execution engine in FaCT

  Currently, mostly because it is implemented in pure Rust, the execution
  engine only pretends to be constant-time. For true constant-time computation,
  you would need to implement the engine in a language, DSL, or assembly that
  ensure constant-time operations.

  FaCT provides a DSL for this purpose. Implementing the engine in FaCT would
  allow the engine, itself, to be verifiably constant-time.

- JIT the execution engine

  This may be more difficult than an interpreter, but there's nothing stopping
  the engine from JITing constant-time instructions.

- Leverage SIMD instructions in the execution engine

  Currently, the execution engine only simulates SIMD instructions. This has
  a small benefit, as it does decrease the amount of bytecode that needs to be
  decoded, but in theory the operations could be truely parallelized via actual
  SIMD hardware.

- Secret containers/tuples

  Currently there is some overhead packing/unpacking secret-u types, a
  `SecretU8` takes up roughly the same space of `Either<u8, Rc<_>>`.
  Secrecy-preserving containers/tuples could elide this cost without
  sacrificing secrecy.

[secret_integers]: https://github.com/hacspec/rust-secret-integers
[CT-Wasm]: https://github.com/PLSysSec/ct-wasm
[FaCT]: https://github.com/PLSysSec/FaCT
[boolean_expression]: https://github.com/cfallin/boolean_expression
[packed_simd]: https://github.com/rust-lang/packed_simd

