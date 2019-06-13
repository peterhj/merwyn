extern crate merwyn;

use merwyn::lang::{HLexer, HParser};

#[test]
fn test_lang() {
  let lexer = HLexer::new("1+2*3");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
  let lexer = HLexer::new("1+(2+3)*4");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
  let lexer = HLexer::new("1+2[3]*4");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
  let lexer = HLexer::new("1+2[(3*4)]");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
  let lexer = HLexer::new("1+2*3[]");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
  let lexer = HLexer::new("1+2*3[4,5]");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
  let lexer = HLexer::new("1+2*3[4,5,6]");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
  //panic!();
}

#[test]
fn test_lang_alias() {
  let lexer = HLexer::new("(x[0] + 1, 2) as y");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_concat() {
  let lexer = HLexer::new("x ++ y");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_concat_2() {
  let lexer = HLexer::new("(x, y, z) as w ++ _");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_cons() {
  let lexer = HLexer::new("x :: y");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_cons_2() {
  let lexer = HLexer::new("x :: y :: z :: _");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_differential() {
  let lexer = HLexer::new("D[x]");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_ident_infix() {
  let lexer = HLexer::new("1 `add 2");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_ident_prime() {
  let lexer = HLexer::new("asdf'");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_ident_prime_2() {
  let lexer = HLexer::new("asdf''");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_literal_logical_bot() {
  let lexer = HLexer::new("bot");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_literal_logical_tee() {
  let lexer = HLexer::new("tee");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

// TODO: deprecated logical syntax.
/*#[test]
fn test_lang_logical() {
  let lexer = HLexer::new("let y = p[x] | q[x] ^ r[x] | s[x]; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}*/

#[test]
fn test_lang_logical_short() {
  let lexer = HLexer::new("let y = p[x] || q[x] ^^ r[x] || s[x]; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let() {
  let lexer = HLexer::new("let asdf[x] = 1; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_lam0() {
  let lexer = HLexer::new("let f = \\. asdf; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_match() {
  let lexer = HLexer::new("let match (a, b) = x; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_pub() {
  let lexer = HLexer::new("pub let asdf[x] = 1; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_rec() {
  let lexer = HLexer::new("let rec asdf[x] = asdf[x]; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_samples() {
  let lexer = HLexer::new("let z ~ standard_normal; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_empty() {
  let lexer = HLexer::new("let asdf[x]; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_where() {
  let lexer = HLexer::new("let asdf[x] where p[x] = 1; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_where_2() {
  let lexer = HLexer::new("let asdf[x] where p[x], q[x] = 1; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_where_3() {
  let lexer = HLexer::new("let asdf[x] where p[x], q[x], r[x] = 1; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_where_4() {
  let lexer = HLexer::new("let asdf[x] where p[x] == q[x], r[x] = 1; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_if() {
  let lexer = HLexer::new("let asdf[x] :- 1; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_if_2() {
  let lexer = HLexer::new("let asdf[x] :- 1, 2; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_let_for_if() {
  let lexer = HLexer::new("let asdf[x] for y, z :- p[x,y], q[x,z]; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_match() {
  let lexer = HLexer::new("match x | 1 => a | tee => b[1,a] | () => \\c. 2*c | _ => \\y, z. match y | 1 => 2 | _ => 1");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_tuple() {
  let lexer = HLexer::new("(1, 2, x, y)");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_tylam() {
  let lexer = HLexer::new("let x[y,z]: ['a, 'b] -> 'c = 0 in 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_tyvar() {
  let lexer = HLexer::new("let x: 'a = 0 in 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}

#[test]
fn test_lang_where_let() {
  let lexer = HLexer::new("where let asdf[x] = 1; 0");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("{:?}", htree);
}
