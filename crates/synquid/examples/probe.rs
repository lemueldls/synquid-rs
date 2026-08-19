use std::time::Instant;

use synquid::{parser::parse_program, pretty::show_doc};

fn probe(name: &str, input: &str) {
    let start = Instant::now();
    println!("=== {name}: parsing ...");
    match parse_program(input, name) {
        Ok(decls) => println!("    ok: {} decls in {:?}", decls.len(), start.elapsed()),
        Err(e) => {
            println!(
                "    err: {} at {}:{}",
                show_doc(&e.description),
                e.position.line,
                e.position.column
            );
        }
    }
}

fn main() {
    let replicate = "\
type Nat = {Int | _v >= 0}

data List a where
\tNil :: List a
\tCons :: x: a -> xs: List a -> List a

termination measure len :: List a -> {Int | _v >= 0} where
  Nil -> 0
  Cons x xs -> 1 + len xs

zero :: {Int | _v == 0}
inc :: x: Int -> {Int | _v == x + 1}
dec :: x: Int -> {Int | _v == x - 1}
leq :: x: Int -> y: Int -> {Bool | _v == (x <= y)}
neq :: x: Int -> y: Int -> {Bool | _v == (x != y)}

replicate :: n: Nat -> x: a -> {List a | len _v == n}
replicate = ??
";

    let delete = "\
data List a where
\tNil :: List a
\tCons :: x: a -> xs: List a -> List a

termination measure len :: List a -> {Int | _v >= 0} where
  Nil -> 0
  Cons x xs -> 1 + len xs

measure elems :: List a -> Set a where
  Nil -> []
  Cons x xs -> [x] + elems xs

eq :: x: a -> y: a -> {Bool | _v == (x == y)}
neq :: x: a -> y: a -> {Bool | _v == (x != y)}

delete :: x: a -> xs: List a -> {List a | elems _v == elems xs - [x]}
delete = \\x . \\xs .
    match xs with
      Nil -> xs
      Cons x3 x4 ->
        if x3 == x
          then delete x x4
          else Cons x3 (delete x x4)
";

    probe("empty", "");
    probe("whitespace-only", "   \n\n  -- comment only\n");

    probe("replicate", replicate);
    probe("delete", delete);

    probe(
        "type-shapes",
        "f :: List a -> Int\n\
         g :: x: Int -> {Int | _v > 0} -> {Int | _v >= x}\n\
         h :: [Int] -> Bool\n",
    );

    probe(
        "forall-setops",
        "elemIndex :: <p :: Int -> a -> Bool> . x: a -> xs: {List a <p> | x in elems _v} -> {Int | p _v x}\n\
         qualifier {x <= y, x != y}\n",
    );

    probe(
        "precedence",
        "inline abs x = if x >= 0 then x else -x\n\
         inline f a b = 1 + 2 * 3\n\
         inline g a b = a ==> b ==> c\n\
         inline h a b = a <= b && c <= d\n\
         inline i a b = x in elems _v\n",
    );

    probe(
        "match-annot",
        "foo = \\x . let y = x in if x then (y :: Bool) else error\n\
         bar = match x with\n  Nil -> [1, 2, 3]\n  Cons a b -> (\\z . z) ??\n",
    );

    probe(
        "data-pred",
        "data Foo a <p :: a -> Bool> ! where\n\tA :: Foo a\ndata Bar a <p :: a -> a -> Bool> where\n\tB :: Bar a\n",
    );

    probe(
        "indent-violations-partial",
        "measure len :: List a -> Int where\nNil -> 0\n",
    );

    probe(
        "measure-const-args",
        "termination measure count :: n: Int -> List a -> {Int | _v == n} where\n  Nil -> n\n  Cons x xs -> count (n + 1) xs\n",
    );

    probe(
        "sort-shapes",
        "f :: Int -> Bool -> Int -> Int\ng :: Set a -> List (a) -> Int\n",
    );

    probe(
        "crlf",
        "{- block comment\r\nspanning lines -}\r\nf :: Int -> Int\r\n-- trailing comment\r\ng = 5\r\n",
    );
}
