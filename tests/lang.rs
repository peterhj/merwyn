extern crate hebb;

use hebb::lang::{HLexer, HParser};

#[test]
fn test_lang() {
  let lexer = HLexer::new("1+2*3");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
  let lexer = HLexer::new("1+(2+3)*4");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
  let lexer = HLexer::new("1+2[3]*4");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
  let lexer = HLexer::new("1+2[(3*4)]");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
  let lexer = HLexer::new("1+2*3[]");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
  let lexer = HLexer::new("1+2*3[4,5]");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
  let lexer = HLexer::new("1+2*3[4,5,6]");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
  //panic!();
}

#[test]
fn test_lang_lexeme_ident_infix() {
  let lexer = HLexer::new("1 `add 2");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}

#[test]
fn test_lang_lexeme_ident_prime() {
  let lexer = HLexer::new("asdf'");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}

#[test]
fn test_lang_lexeme_ident_prime_2() {
  let lexer = HLexer::new("asdf''");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}

#[test]
fn test_lang_literal_logical_bot() {
  let lexer = HLexer::new("bot");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}

#[test]
fn test_lang_literal_logical_tee() {
  let lexer = HLexer::new("tee");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}

#[test]
fn test_lang_logical() {
  let lexer = HLexer::new("let y = p[x] | q[x] ^ r[x] | s[x]; 0");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}

#[test]
fn test_lang_logical_short() {
  let lexer = HLexer::new("let y = p[x] || q[x] ^^ r[x] || s[x]; 0");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}

#[test]
fn test_lang_let() {
  let lexer = HLexer::new("let asdf[x] = 1; 0");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}

#[test]
fn test_lang_let_pub() {
  let lexer = HLexer::new("pub let asdf[x] = 1; 0");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}

#[test]
fn test_lang_let_samples() {
  let lexer = HLexer::new("let z ~ standard_normal; 0");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}

#[test]
fn test_lang_let_empty() {
  let lexer = HLexer::new("let asdf[x]; 0");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}

#[test]
fn test_lang_let_where() {
  let lexer = HLexer::new("let asdf[x] where p[x] = 1; 0");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}

#[test]
fn test_lang_let_where_2() {
  let lexer = HLexer::new("let asdf[x] where p[x], q[x] = 1; 0");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}

#[test]
fn test_lang_let_where_3() {
  let lexer = HLexer::new("let asdf[x] where p[x], q[x], r[x] = 1; 0");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}

#[test]
fn test_lang_let_where_4() {
  let lexer = HLexer::new("let asdf[x] where p[x] == q[x], r[x] = 1; 0");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}

#[test]
fn test_lang_let_if() {
  let lexer = HLexer::new("let asdf[x] :- 1; 0");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}

#[test]
fn test_lang_let_if_2() {
  let lexer = HLexer::new("let asdf[x] :- 1, 2; 0");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}

#[test]
fn test_lang_let_for_if() {
  let lexer = HLexer::new("let asdf[x] for y, z :- p[x,y], q[x,z]; 0");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}

#[test]
fn test_lang_where_let() {
  let lexer = HLexer::new("where let asdf[x] = 1; 0");
  let parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
}
