extern crate merwyn;

use merwyn::lang::{HLexer, HParser};

#[should_panic]
#[test]
fn test_lang_empty() {
  let lexer = HLexer::new("");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[should_panic]
#[test]
fn test_lang_empty_2() {
  let lexer = HLexer::new(" ");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[should_panic]
#[test]
fn test_lang_empty_comment_doc() {
  let lexer = HLexer::new(
"-- | "
  );
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[should_panic]
#[test]
fn test_lang_empty_comment_doc_2() {
  let lexer = HLexer::new(
"---| "
  );
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[should_panic]
#[test]
fn test_lang_empty_comment_doc_3() {
  let lexer = HLexer::new(
"---  | "
  );
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[should_panic]
#[test]
fn test_lang_empty_comment_eol() {
  let lexer = HLexer::new(
"-- "
  );
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[should_panic]
#[test]
fn test_lang_empty_comment_multi() {
  let lexer = HLexer::new(
"(--

--)"
  );
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[should_panic]
#[test]
fn test_lang_error() {
  let lexer = HLexer::new("let x = 1 = 2");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_examples() {
  let lexer = HLexer::new("1+2*3");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
  let lexer = HLexer::new("1+(2+3)*4");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
  let lexer = HLexer::new("1+2[3]*4");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
  let lexer = HLexer::new("1+2[(3*4)]");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
  let lexer = HLexer::new("1+2*3[]");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
  let lexer = HLexer::new("1+2*3[4,5]");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
  let lexer = HLexer::new("1+2*3[4,5,6]");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
  //panic!();
}

#[test]
fn test_lang_alias() {
  let lexer = HLexer::new("(x[0] + 1, 2) as y");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_alt() {
  let lexer = HLexer::new(r"alt f in let alt f: [Flp, Int] -> Flp = \x, k -> x in f[_]");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_alt_2() {
  let lexer = HLexer::new(r"alt f in let alt f: [Int] -> Int = \x -> x in let alt f: [Flp] -> Flp = \x -> x in f[_]");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_concat() {
  let lexer = HLexer::new("x ++ y");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_concat_2() {
  let lexer = HLexer::new("(x, y, z) as w ++ _");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

// XXX: deprecated cons syntax.
/*#[test]
fn test_lang_cons() {
  let lexer = HLexer::new("x :: y");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_cons_2() {
  let lexer = HLexer::new("x :: y :: z :: _");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}*/

#[test]
fn test_lang_derivative_adjoint() {
  let lexer = HLexer::new("D[y]");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_derivative_tangent() {
  let lexer = HLexer::new("D'[y]");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[should_panic]
#[test]
fn test_lang_dim() {
  let lexer = HLexer::new("(3.14, 42. i, 137f j, -1. k");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_group_paren() {
  let lexer = HLexer::new("(x)");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_group_paren_2() {
  let lexer = HLexer::new("((a) + ((x) + (y)))");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_ident() {
  let lexer = HLexer::new("asdf");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_ident_1() {
  let lexer = HLexer::new("asdf'");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_ident_2() {
  let lexer = HLexer::new("asdf''");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_ident_infix() {
  let lexer = HLexer::new("1 `add 2");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_ident_postfix() {
  let lexer = HLexer::new("x ^T");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_ident_cryptic() {
  let lexer = HLexer::new("~=Az/09+==");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_ident_use() {
  let lexer = HLexer::new("~asdf");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_ident_use_2() {
  let lexer = HLexer::new("~example.net:asdf");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_jacobian() {
  let lexer = HLexer::new("J[y]");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

//#[should_panic]
#[test]
fn test_lang_jacobian_t() {
  let lexer = HLexer::new("J'[y]");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_literal_flo() {
  let lexer = HLexer::new("3.14");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_literal_flo_2() {
  let lexer = HLexer::new("3.14f");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_literal_flo_3() {
  let lexer = HLexer::new("3f");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_literal_int() {
  let lexer = HLexer::new("3");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_literal_int_2() {
  let lexer = HLexer::new("3n");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_literal_logical_false() {
  let lexer = HLexer::new("false");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_literal_logical_truth() {
  let lexer = HLexer::new("truth");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

// XXX: deprecated logical syntax.
/*#[test]
fn test_lang_logical() {
  let lexer = HLexer::new("let y = p[x] | q[x] ^ r[x] | s[x]; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}*/

#[test]
fn test_lang_logical_short() {
  let lexer = HLexer::new(r"let t = p[x] \/ q[x] /\ r[x] \/ s[x]; t");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_fun() {
  let lexer = HLexer::new("let asdf[x] = 1; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_lam() {
  let lexer = HLexer::new(r"let f = \ -> asdf; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_stup() {
  let lexer = HLexer::new("let (a, b) = x; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_tup() {
  let lexer = HLexer::new("let (|a, b|) = x; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

// TODO: pub syntax pending.
/*#[test]
fn test_lang_let_pub() {
  let lexer = HLexer::new("pub let asdf[x] = 1; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}*/

#[test]
fn test_lang_let_rec() {
  let lexer = HLexer::new("let rec asdf[x] = asdf[x]; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

// XXX: deprecated logical syntax.
/*#[test]
fn test_lang_let_samples() {
  let lexer = HLexer::new("let z ~ standard_normal; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}*/

// TODO: status of let syntax variants is pending.
/*#[test]
fn test_lang_let_empty() {
  let lexer = HLexer::new("let asdf[x]; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_where() {
  let lexer = HLexer::new("let asdf[x] where p[x] = 1; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_where_2() {
  let lexer = HLexer::new("let asdf[x] where p[x], q[x] = 1; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_where_3() {
  let lexer = HLexer::new("let asdf[x] where p[x], q[x], r[x] = 1; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_where_4() {
  let lexer = HLexer::new("let asdf[x] where p[x] == q[x], r[x] = 1; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_if() {
  let lexer = HLexer::new("let asdf[x] :- 1; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_if_2() {
  let lexer = HLexer::new("let asdf[x] :- 1, 2; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_for_if() {
  let lexer = HLexer::new("let asdf[x] for y, z :- p[x,y], q[x,z]; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}*/

#[test]
fn test_lang_match() {
  let lexer = HLexer::new(r"match x with | 1 => a | truth => b[1,a] | () => \c -> 2*c | _ => \y, z -> match y with | 1 => 2 | _ => 1");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_op_bang() {
  let lexer = HLexer::new("x!");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_op_bang_2() {
  let lexer = HLexer::new("-x!");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[should_panic]
#[test]
fn test_lang_partial_derivative_prime() {
  let lexer = HLexer::new("d'[y].x");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_partial_derivative() {
  let lexer = HLexer::new("d[y].x");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

/*#[test]
fn test_lang_partial_derivative_2() {
  let lexer = HLexer::new("d[(f, g)].{x, y}");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}*/

#[test]
fn test_lang_partial_derivative_variant() {
  let lexer = HLexer::new("d.x[y]");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_partial_derivative_variant_2() {
  let lexer = HLexer::new("d.{x, y}[(f, g)]");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_quote() {
  let lexer = HLexer::new("'x");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_quote_2() {
  let lexer = HLexer::new("'x + y");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_quote_3() {
  let lexer = HLexer::new("'(x + y)");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_quote_unquote() {
  let lexer = HLexer::new("'?(x + y)");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_quote_unquote_2() {
  let lexer = HLexer::new("'(?x + ?(y))");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_tuple_s() {
  let lexer = HLexer::new("()");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_tuple_s_1() {
  let lexer = HLexer::new("(1,)");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_tuple_s_2() {
  let lexer = HLexer::new("(1, 2, x, y)");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_tuple_s_3() {
  let lexer = HLexer::new("(1, 2, x, y,)");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_tuple_u() {
  let lexer = HLexer::new("(|1, 2, x, y|)");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

#[test]
fn test_lang_tylam() {
  let lexer = HLexer::new("let x[y,z]: [a, Flp] -> [x] -> Int = 0 in 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}

// TODO: quote syntax is being reused.
/*#[test]
fn test_lang_tyvar() {
  let lexer = HLexer::new("let x: 'a = 0 in 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}*/

// TODO: status of where syntax pending.
/*#[test]
fn test_lang_where_let() {
  let lexer = HLexer::new("where let asdf[x] = 1; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("{:?}", htree);
}*/
