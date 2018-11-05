extern crate hebb;

use hebb::lang::{HLexer, HParser};

#[test]
fn test_lang() {
  let lexer = HLexer::new("1+2*3");
  let mut parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
  let lexer = HLexer::new("1+(2+3)*4");
  let mut parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
  let lexer = HLexer::new("1+2[3]*4");
  let mut parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
  let lexer = HLexer::new("1+2[(3*4)]");
  let mut parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
  let lexer = HLexer::new("1+2*3[]");
  let mut parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
  let lexer = HLexer::new("1+2*3[4,5]");
  let mut parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
  let lexer = HLexer::new("1+2*3[4,5,6]");
  let mut parser = HParser::new(lexer);
  let ast = parser.parse();
  println!("{:?}", ast);
  //panic!();
}
