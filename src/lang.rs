// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use plex::{lexer};

use std::rc::{Rc};

lexer! {
  fn next_token(text: 'a) -> HLToken;

  r#"\n"#           => HLToken::Newline,
  r#"[ \t\r]+"#     => HLToken::Whitespace,
  r#"#[^\n]*"#      => HLToken::EolComment,
  r#"\([*](~(.*[*]\).*))[*]\)"# => HLToken::MultilineComment(0),

  r#"end"#          => HLToken::End,
  r#"break"#        => HLToken::Break,
  r#"return"#       => HLToken::Return,
  //r#"trace"#        => HLToken::Trace,
  r#"module"#       => HLToken::Module,
  r#"include"#      => HLToken::Include,
  r#"require"#      => HLToken::Require,
  /*r#"d'["#          => HLToken::DMinorPrimeBrack,
  r#"d["#           => HLToken::DMinorBrack,
  r#"D'["#          => HLToken::DMajorPrimeBrack,
  r#"D["#           => HLToken::DMajorBrack,
  r#"J'["#          => HLToken::JMajorPrimeBrack,
  r#"J["#           => HLToken::JMajorBrack,*/
  r#"d'"#           => HLToken::DMinorPrime,
  r#"d"#            => HLToken::DMinor,
  r#"D'"#           => HLToken::DMajorPrime,
  r#"D"#            => HLToken::DMajor,
  r#"J'"#           => HLToken::JMajorPrime,
  r#"J"#            => HLToken::JMajor,
  r#"adj"#          => HLToken::Adj,
  r#"tng"#          => HLToken::Tng,
  r#"alt"#          => HLToken::Alt,
  //r#"alternate"#    => HLToken::Alt,
  r#"const"#        => HLToken::Const,
  r#"export"#       => HLToken::Export,
  r#"def"#          => HLToken::Def,
  r#"dyn"#          => HLToken::Dyn,
  r#"gen"#          => HLToken::Gen,
  //r#"generic"#      => HLToken::Gen,
  r#"import"#       => HLToken::Import,
  //r#"lambda"#       => HLToken::Lambda,
  r#"let"#          => HLToken::Let,
  r#"pub"#          => HLToken::Pub,
  r#"rec"#          => HLToken::Rec,
  r#"ref"#          => HLToken::Ref,
  r#"rnd"#          => HLToken::Rnd,
  r#"seq"#          => HLToken::Seq,
  r#"in"#           => HLToken::In,
  r#"as"#           => HLToken::As,
  r#"where"#        => HLToken::Where,
  r#"for"#          => HLToken::For,
  r#"switch"#       => HLToken::Switch,
  r#"match"#        => HLToken::Match,
  r#"λ"#            => HLToken::Lambda,
  r#":-"#           => HLToken::If,
  r#":="#           => HLToken::Assigns,
  r#"<="#           => HLToken::LtEquals,
  r#"<"#            => HLToken::Lt,
  r#">="#           => HLToken::GtEquals,
  r#">"#            => HLToken::Gt,
  r#"/="#           => HLToken::NotEquals,
  r#"==>"#          => HLToken::RDDArrow,
  r#"=>"#           => HLToken::RDArrow,
  r#"=="#           => HLToken::EqEquals,
  r#"="#            => HLToken::Equals,
  r#"\~"#           => HLToken::Tilde,
  r#"\\"#           => HLToken::Backslash,
  r#"\.\+"#         => HLToken::DotPlus,
  r#"\.-"#          => HLToken::DotDash,
  r#"\.\*"#         => HLToken::DotStar,
  r#"\./"#          => HLToken::DotSlash,
  r#"\.\("#         => HLToken::LDotParen,
  r#"\.\["#         => HLToken::LDotBrack,
  r#"\.\{"#         => HLToken::LDotCurly,
  r#"\.\.\."#       => HLToken::Ellipsis,
  r#"\.\."#         => HLToken::DotDot,
  r#"\."#           => HLToken::Dot,
  r#","#            => HLToken::Comma,
  r#";;"#           => HLToken::SemiSemi,
  r#";"#            => HLToken::Semi,
  r#"::"#           => HLToken::ColonColon,
  r#":"#            => HLToken::Colon,
  r#"\|>"#          => HLToken::RPipe,
  r#"\|\|"#         => HLToken::BarBar,
  r#"\|"#           => HLToken::Bar,
  r#"^^"#           => HLToken::HatHat,
  r#"^"#            => HLToken::Hat,
  r#"\+\+"#         => HLToken::PlusPlus,
  r#"\+:"#          => HLToken::PlusColon,
  r#"\+\."#         => HLToken::PlusDot,
  r#"\+"#           => HLToken::Plus,
  //r#"-:"#           => HLToken::Then,
  r#"-o"#           => HLToken::ROArrow,
  r#"->"#           => HLToken::RArrow,
  r#"-:"#           => HLToken::DashColon,
  r#"-\."#          => HLToken::DashDot,
  r#"-"#            => HLToken::Dash,
  r#"\*:"#          => HLToken::StarColon,
  r#"\*\."#         => HLToken::StarDot,
  r#"\*"#           => HLToken::Star,
  r#"/:"#           => HLToken::SlashColon,
  r#"/\."#          => HLToken::SlashDot,
  r#"/"#            => HLToken::Slash,
  //r#"\{\}"#         => HLToken::NilSTupLit,
  //r#"\(\)"#         => HLToken::NilTupLit,
  r#"\(\|"#         => HLToken::LParenBar,
  r#"\("#           => HLToken::LParen,
  r#"\|\)"#         => HLToken::RParenBar,
  r#"\)"#           => HLToken::RParen,
  r#"\["#           => HLToken::LBrack,
  r#"\]"#           => HLToken::RBrack,
  r#"\{"#           => HLToken::LCurly,
  r#"\}"#           => HLToken::RCurly,

  r#"_"#            => HLToken::PlacePat,

  r#"'_"#           => HLToken::PlaceTy,
  r#"'\?"#          => HLToken::TopTy,
  r#"Bit"#          => HLToken::BitTy,
  r#"Int"#          => HLToken::IntTy,
  r#"Flp"#          => HLToken::FlpTy,
  //r#"Flp16"#        => HLToken::Flp16Ty,
  //r#"Flp32"#        => HLToken::Flp32Ty,
  //r#"Fmp"#          => HLToken::FmpTy,

  r#"unit"#         => HLToken::UnitLit,
  r#"tee"#          => HLToken::TeeLit,
  r#"bot"#          => HLToken::BotLit,

  //r#"[0-9]+\.[0-9]*[fp16]"# => HLToken::Flp16Lit(text[ .. text.len() - 1].parse().unwrap()),
  //r#"[0-9]+\.[0-9]*[fp32]"# => HLToken::Flp32Lit(text[ .. text.len() - 1].parse().unwrap()),
  //r#"[0-9]+\.[0-9]*[fmp]"#  => HLToken::FmpLit(text[ .. text.len() - 1].parse().unwrap()),
  r#"[0-9]+\.[0-9]*[f]"#    => HLToken::FlpLit(text[ .. text.len() - 1].parse().unwrap()),
  r#"[0-9]+\.[0-9]*"#       => HLToken::FlpLit(text.parse().unwrap()),
  r#"[0-9]+[f]"#            => HLToken::FlpLit(text[ .. text.len() - 1].parse().unwrap()),
  r#"[0-9]+[n]"#            => HLToken::IntLit(text[ .. text.len() - 1].parse().unwrap()),
  r#"[0-9]+"#               => HLToken::IntLit(text.parse().unwrap()),

  r#"[a-zA-Z_][a-zA-Z0-9_]*[']*"#   => HLToken::Ident(text.to_owned()),
  r#"`[a-zA-Z_][a-zA-Z0-9_]*[']*"#  => HLToken::InfixIdent(text.to_owned()),
  r#"\?[a-zA-Z_][a-zA-Z0-9_]*[']*"# => HLToken::ImplicitIdent(text.to_owned()),
  r#"\?[0-9]+"#                     => HLToken::ImplicitIndex(text.parse().unwrap()),
  r#"'[a-zA-Z_][a-zA-Z0-9_]*[']*"#  => HLToken::TyvarIdent(text.to_owned()),
  r#"\~[A-Za-z0-9/\+]+[=]*"#        => HLToken::CrypticIdent(text.to_owned()),
  r#"@[a-z0-9\-\.]+[:][a-z0-9\-]+"# => HLToken::UseIdent(text.to_owned()),
  r#"@[a-z0-9\-]+"#                 => HLToken::UseIdent(text.to_owned()),

  r#"."#            => HLToken::_Eof,
}

#[derive(Clone, PartialEq, Debug)]
pub enum HLToken {
  Newline,
  Whitespace,
  EolComment,
  MultilineComment(usize),
  End,
  Break,
  Return,
  Trace,
  Module,
  Include,
  Require,
  Export,
  Import,
  DMajor,
  DMajorPrime,
  DMinor,
  DMinorPrime,
  JMajor,
  JMajorPrime,
  /*DMajorBrack,
  DMajorPrimeBrack,
  DMinorBrack,
  DMinorPrimeBrack,
  JMajorBrack,
  JMajorPrimeBrack,*/
  Adj,
  Tng,
  Dyn,
  Pub,
  Ref,
  Def,
  Let,
  Alt,
  Const,
  Gen,
  Rec,
  Rnd,
  Seq,
  In,
  As,
  Where,
  For,
  Switch,
  Match,
  Lambda,
  If,
  Assigns,
  Equals,
  EqEquals,
  NotEquals,
  Gt,
  GtEquals,
  Lt,
  LtEquals,
  Tilde,
  Backslash,
  Dot,
  DotDot,
  DotPlus,
  DotDash,
  DotStar,
  DotSlash,
  Ellipsis,
  Comma,
  Semi,
  SemiSemi,
  Colon,
  ColonColon,
  Bar,
  BarBar,
  Hat,
  HatHat,
  Plus,
  PlusDot,
  PlusColon,
  PlusPlus,
  Dash,
  DashDot,
  DashColon,
  RArrow,
  RDArrow,
  RDDArrow,
  ROArrow,
  RPipe,
  Star,
  StarDot,
  StarColon,
  Slash,
  SlashDot,
  SlashColon,
  LDotParen,
  LParenBar,
  RParenBar,
  LParen,
  RParen,
  LDotBrack,
  LBrack,
  RBrack,
  LDotCurly,
  LCurly,
  RCurly,
  PlacePat,
  PlaceTy,
  TopTy,
  BitTy,
  IntTy,
  FlpTy,
  TyvarIdent(String),
  UnitLit,
  //NilSTupLit,
  //NilTupLit,
  TeeLit,
  BotLit,
  IntLit(i64),
  FlpLit(f64),
  Ident(String),
  InfixIdent(String),
  ImplicitIdent(String),
  ImplicitIndex(i64),
  CrypticIdent(String),
  UseIdent(String),
  _Eof,
}

#[derive(Clone, Debug)]
pub struct HLTokenInfo<'src> {
  //pub filename: Option<String>,
  pub line_nr:  usize,
  pub line_pos: usize,
  pub text:     Option<&'src str>,
}

#[derive(Clone, Debug)]
pub struct HLexer<'src> {
  original: &'src str,
  remnant:  &'src str,
  line_nr:  usize,
  line_pos: usize,
  next_pos: usize,
  eof:      bool,
}

impl<'src> HLexer<'src> {
  pub fn new(src: &'src str, /*srcinfo: HLSourceInfo*/) -> HLexer<'src> {
    HLexer{
      original: src,
      remnant:  src,
      line_nr:  0,
      line_pos: 0,
      next_pos: 0,
      eof:      false,
    }
  }
}

impl<'src> Iterator for HLexer<'src> {
  //type Item = HLToken;
  //type Item = (HLToken, Option<&'src str>);
  type Item = (HLToken, HLTokenInfo<'src>);

  //fn next(&mut self) -> Option<HLToken> {
  //fn next(&mut self) -> Option<(HLToken, Option<&'src str>)> {
  fn next(&mut self) -> Option<(HLToken, HLTokenInfo<'src>)> {
    loop {
      if self.eof {
        let tok_info = HLTokenInfo{
          line_nr:    self.line_nr,
          line_pos:   self.line_pos,
          text:       None,
        };
        return Some((HLToken::_Eof, tok_info));
      }
      let (tok, tok_text) = if let Some((tok, next_remnant)) = next_token(self.remnant) {
        let tok_off = unsafe { next_remnant.as_ptr().offset_from(self.remnant.as_ptr()) };
        assert!(tok_off >= 0);
        let tok_len = tok_off as usize;
        let tok_text = self.remnant.get(0 .. tok_len);
        /*let src_off = unsafe { next_remnant.as_ptr().offset_from(self.original.as_ptr()) };
        assert!(src_off >= 0);
        let tok_src_off = src_off as usize;*/
        self.remnant = next_remnant;
        self.line_pos = self.next_pos;
        self.next_pos += tok_len;
        (tok, tok_text)
      } else {
        self.line_pos = self.next_pos;
        self.eof = true;
        (HLToken::_Eof, None)
      };
      match (tok, tok_text) {
        (HLToken::Newline, Some(_)) => {
          self.line_nr += 1;
          self.line_pos = 0;
          self.next_pos = 0;
          continue;
        }
        (HLToken::Whitespace, Some(_)) |
        (HLToken::EolComment, Some(_)) => {
          continue;
        }
        (HLToken::MultilineComment(_), Some(text)) => {
          let mut eol_iter = text.rmatch_indices('\n');
          let (line_ct, line_off) = match eol_iter.next() {
            None => (0, text.len()),
            Some((last_pos, _)) => {
              (1 + eol_iter.count(), text.len() - 1 - last_pos)
            }
          };
          self.line_nr += line_ct;
          self.line_pos = line_off;
          self.next_pos = line_off;
          continue;
        }
        /*(HLToken::_Err, Some(_)) => {
          // TODO
          panic!();
        }*/
        /*(HLToken::_Eof, None) => {
          return Some((HLToken::_Eof, None));
        }*/
        (tok, tok_text) => {
          let tok_info = HLTokenInfo{
            line_nr:    self.line_nr,
            line_pos:   self.line_pos,
            text:       tok_text,
          };
          return Some((tok, tok_info));
        }
        _ => unreachable!(),
      }
    }
  }
}

#[derive(Clone, Default, Debug)]
pub struct HLetDecorators {
  pub pub_: bool,
  pub alt:  bool,
  pub gen:  bool,
  pub rec:  bool,
  //pub rnd:  bool,
  pub seq:  bool,
  pub ty:   Option<Rc<HExpr>>,
}

#[derive(Clone, Debug)]
pub enum HTypat {
  TopTy,
  PlaceTy,
  Tyvar(String),
  FunTy(Vec<Rc<HTypat>>, Rc<HTypat>),
  BitTy,
  IntTy,
  FlpTy,
  UnitTy,
  Ident(String),
}

#[derive(Clone, Debug)]
pub enum HError {
  Eof,
  Unknown,
  Unexpected(HLToken),
  Expected(Vec<HLToken>, HLToken),
  MissingMatchArms,
  Other,
}

#[derive(Clone, Debug)]
pub enum HExpr {
  End,
  //Export(Rc<HExpr>, Option<Rc<HExpr>>, Rc<HExpr>),
  //Import(String, Rc<HExpr>),
  Break(Rc<HExpr>),
  Lambda(Vec<Rc<HExpr>>, Rc<HExpr>),
  Apply(Rc<HExpr>, Vec<Rc<HExpr>>),
  ETuple(Vec<Rc<HExpr>>),
  STuple(Vec<Rc<HExpr>>),
  Tuple(Vec<Rc<HExpr>>),
  PartialD(Rc<HExpr>),
  PartialAltD(Rc<HExpr>, Rc<HExpr>),
  AdjointD(Rc<HExpr>),
  TangentD(Rc<HExpr>),
  //DirectionalD(Rc<HExpr>, Rc<HExpr>),
  Jacobian(Rc<HExpr>),
  Adj(Rc<HExpr>),
  Tng(Rc<HExpr>),
  AdjDyn(Rc<HExpr>),
  Const(Rc<HExpr>),
  Let(Option<HLetDecorators>, Option<Rc<HExpr>>, Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  Alt_(Rc<HExpr>, Rc<HExpr>),
  Alt(Option<HLetDecorators>, /*Rc<HExpr>,*/ Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  //LetFun(Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  //LetMatch(Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  LetRand(Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  LetEmpty(Rc<HExpr>, Rc<HExpr>),
  LetWhere(Rc<HExpr>, Vec<Rc<HExpr>>, Rc<HExpr>, Rc<HExpr>),
  LetIf(Rc<HExpr>, Vec<Rc<HExpr>>, Rc<HExpr>),
  LetForIf(Rc<HExpr>, Vec<Rc<HExpr>>, Vec<Rc<HExpr>>, Rc<HExpr>),
  WhereLet(Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  Switch(Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  Match(Rc<HExpr>, Vec<(Rc<HExpr>, Rc<HExpr>)>),
  Alias(Rc<HExpr>, Rc<HExpr>),
  ShortOr(Rc<HExpr>, Rc<HExpr>),
  ShortAnd(Rc<HExpr>, Rc<HExpr>),
  Eq(Rc<HExpr>, Rc<HExpr>),
  NotEq(Rc<HExpr>, Rc<HExpr>),
  Gt(Rc<HExpr>, Rc<HExpr>),
  GtEq(Rc<HExpr>, Rc<HExpr>),
  Lt(Rc<HExpr>, Rc<HExpr>),
  LtEq(Rc<HExpr>, Rc<HExpr>),
  Or(Rc<HExpr>, Rc<HExpr>),
  And(Rc<HExpr>, Rc<HExpr>),
  Add(Rc<HExpr>, Rc<HExpr>),
  Sub(Rc<HExpr>, Rc<HExpr>),
  Mul(Rc<HExpr>, Rc<HExpr>),
  Div(Rc<HExpr>, Rc<HExpr>),
  Infix(String, Rc<HExpr>, Rc<HExpr>),
  Neg(Rc<HExpr>),
  //Cons(Rc<HExpr>, Rc<HExpr>),
  Concat(Rc<HExpr>, Rc<HExpr>),
  PlacePat,
  /*BitTy,
  IntTy,
  FlpTy,
  Tyvar(String),
  FunTy(Vec<Rc<HTypat>>, Rc<HTypat>),*/
  Typat(Rc<HTypat>),
  UnitLit,
  //NilSTupLit,
  //NilTupLit,
  TeeLit,
  BotLit,
  IntLit(i64),
  FlpLit(f64),
  Ident(String),
  CrypticIdent(String),
  UseIdent(String),
  PathIndex(Rc<HExpr>, usize),
  PathLookup(Rc<HExpr>, String),
  PathELookup(Rc<HExpr>, Rc<HExpr>),
  //KeyLookup(Rc<HExpr>, String),
  //Arrow(Rc<HExpr>, Rc<HExpr>),
}

//pub struct HParser<'src, Toks: Iterator<Item=(HLToken, Option<&'src str>)>> {
pub struct HParser<'src, Toks> {
  toks: Toks,
  //curr: Option<(HLToken, Option<&'src str>)>,
  curr: Option<(HLToken, HLTokenInfo<'src>)>,
  //prev: Option<(HLToken, Option<&'src str>)>,
  prev: Option<(HLToken, HLTokenInfo<'src>)>,
  bt:   bool,
}

//impl<'src, Toks: Iterator<Item=(HLToken, Option<&'src str>)> + Clone> HParser<'src, Toks> {
impl<'src, Toks: Iterator<Item=(HLToken, HLTokenInfo<'src>)> + Clone> HParser<'src, Toks> {
  pub fn new(toks: Toks) -> HParser<'src, Toks> {
    HParser{
      toks: toks,
      curr: None,
      prev: None,
      bt:   false,
    }
  }

  fn backtrack(&mut self) {
    assert!(!self.bt);
    self.bt = true;
  }

  fn advance(&mut self) {
    if self.bt {
      self.bt = false;
    } else {
      self.prev = self.curr.take();
      self.curr = self.toks.next();
    }
  }

  //fn current_token(&mut self) -> (HLToken, Option<&'src str>) {
  fn current_token(&self) -> HLToken {
    if self.bt {
      match self.prev {
        //Some(ref tok) => tok.clone(),
        Some((ref tok, _)) => tok.clone(),
        None => HLToken::_Eof,
      }
    } else {
      match self.curr {
        //Some(ref tok) => tok.clone(),
        Some((ref tok, _)) => tok.clone(),
        None => HLToken::_Eof,
      }
    }
  }

  fn current_token_info(&self) -> Option<HLTokenInfo<'src>> {
    if self.bt {
      match self.prev {
        Some((_, ref info)) => Some((*info).clone()),
        None => None,
      }
    } else {
      match self.curr {
        Some((_, ref info)) => Some((*info).clone()),
        None => None,
      }
    }
  }

  fn lbp(&self, tok: &HLToken) -> i32 {
    // TODO
    match tok {
      &HLToken::End |
      &HLToken::Export |
      &HLToken::Import |
      &HLToken::Module |
      &HLToken::Include |
      &HLToken::Require |
      &HLToken::Break |
      &HLToken::Return |
      &HLToken::Trace |
      &HLToken::DMajor |
      &HLToken::DMajorPrime |
      &HLToken::DMinor |
      &HLToken::DMinorPrime |
      &HLToken::JMajor |
      &HLToken::JMajorPrime |
      &HLToken::Adj |
      &HLToken::Tng |
      &HLToken::Dyn |
      &HLToken::Pub |
      &HLToken::Let |
      &HLToken::Alt |
      &HLToken::Rec |
      &HLToken::Rnd |
      &HLToken::Seq |
      &HLToken::In |
      &HLToken::Where |
      &HLToken::Switch |
      &HLToken::Match |
      &HLToken::If |
      &HLToken::Lambda |
      &HLToken::For |
      &HLToken::Equals |
      &HLToken::Tilde |
      &HLToken::Backslash |
      &HLToken::Comma |
      &HLToken::SemiSemi |
      &HLToken::Semi |
      &HLToken::DashColon |
      &HLToken::RPipe |
      &HLToken::RDArrow |
      &HLToken::Colon |
      &HLToken::Bar => 0,
      &HLToken::RArrow => 100,
      &HLToken::ColonColon => 180,
      &HLToken::PlusPlus => 200,
      &HLToken::BarBar => 300,
      &HLToken::HatHat => 320,
      &HLToken::EqEquals |
      &HLToken::NotEquals |
      &HLToken::Gt |
      &HLToken::GtEquals |
      &HLToken::Lt |
      &HLToken::LtEquals => 400,
      //&HLToken::Bar => 460,
      //&HLToken::BarBar => 460,
      &HLToken::Hat => 480,
      &HLToken::Plus |
      &HLToken::Dash => 500,
      &HLToken::Star |
      &HLToken::Slash => 520,
      &HLToken::InfixIdent(_) => 600,
      &HLToken::As => 700,
      &HLToken::Dot => 800,
      //&HLToken::LParenBar => _,
      &HLToken::RParenBar => 0,
      //&HLToken::LParen => _,
      &HLToken::RParen => 0,
      &HLToken::LBrack => 800,
      &HLToken::RBrack => 0,
      &HLToken::LDotCurly => 800,
      //&HLToken::LCurly => _,
      &HLToken::RCurly => 0,
      &HLToken::UnitLit |
      //&HLToken::NilSTupLit |
      //&HLToken::NilTupLit |
      &HLToken::TeeLit |
      &HLToken::BotLit |
      &HLToken::IntLit(_) |
      &HLToken::FlpLit(_) |
      &HLToken::Ident(_) |
      &HLToken::TyvarIdent(_) => 0,
      &HLToken::_Eof => 0,
      //&HLToken::_Err => 0,
      _ => unimplemented!(),
    }
  }

  fn nud(&mut self, tok: HLToken) -> Result<HExpr, HError> {
    // TODO
    match tok {
      HLToken::_Eof => {
        Err(HError::Eof)
      }
      /*HLToken::_Err => {
        Err(HError::Other)
      }*/
      HLToken::End => {
        Ok(HExpr::End)
      }
      HLToken::Export => {
        // TODO
        unimplemented!();
      }
      HLToken::Import => {
        // TODO
        /*match self.current_token() {
          HLToken::Ident(mod_name) => {
            self.advance();
            match self.current_token() {
              HLToken::In | HLToken::Semi => {}
              _ => panic!(),
            }
            self.advance();
            let e = self.expression(0)?;
            Ok(HExpr::Import(mod_name, Rc::new(e)))
          }
          _ => panic!(),
        }*/
        unimplemented!();
      }
      HLToken::DMajor => {
        match self.current_token() {
          HLToken::LBrack => {}
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::LBrack], t))
        }
        self.advance();
        let e = self.expression(0)?;
        match self.current_token() {
          /*HLToken::Semi => {
            self.advance();
            let dir_e = self.expression(0)?;
            match self.current_token() {
              HLToken::RBrack => {}
              _ => panic!(),
            }
            self.advance();
            return Ok(HExpr::DirectionalD(Rc::new(e), Rc::new(dir_e)));
          }*/
          HLToken::RBrack => {}
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::RBrack], t))
        }
        self.advance();
        Ok(HExpr::AdjointD(Rc::new(e)))
      }
      HLToken::DMajorPrime => {
        match self.current_token() {
          HLToken::LBrack => {}
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::LBrack], t))
        }
        self.advance();
        let e = self.expression(0)?;
        match self.current_token() {
          HLToken::RBrack => {}
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::RBrack], t))
        }
        self.advance();
        Ok(HExpr::TangentD(Rc::new(e)))
      }
      HLToken::DMinor => {
        match self.current_token() {
          HLToken::Dot => {
            self.advance();
            let wrt = self.expression(self.lbp(&HLToken::Dot))?;
            match self.current_token() {
              HLToken::LBrack => {}
              //_ => panic!(),
              t => return Err(HError::Expected(vec![HLToken::LBrack], t))
            }
            self.advance();
            let e = self.expression(0)?;
            match self.current_token() {
              HLToken::RBrack => {}
              //_ => panic!(),
              t => return Err(HError::Expected(vec![HLToken::RBrack], t))
            }
            self.advance();
            Ok(HExpr::PartialAltD(Rc::new(wrt), Rc::new(e)))
          }
          HLToken::LDotCurly => {
            self.advance();
            let mut elems = Vec::new();
            match self.current_token() {
              HLToken::RCurly => {
                self.advance();
              }
              _ => {
                loop {
                  let e = self.expression(0)?;
                  elems.push(Rc::new(e));
                  match self.current_token() {
                    HLToken::Comma => {
                      self.advance();
                    }
                    HLToken::RCurly => {
                      self.advance();
                      break;
                    }
                    //_ => panic!(),
                    t => return Err(HError::Expected(vec![HLToken::Comma, HLToken::RCurly], t))
                  }
                }
              }
            }
            let wrt = HExpr::ETuple(elems);
            match self.current_token() {
              HLToken::LBrack => {}
              //_ => panic!(),
              t => return Err(HError::Expected(vec![HLToken::LBrack], t))
            }
            self.advance();
            let e = self.expression(0)?;
            match self.current_token() {
              HLToken::RBrack => {}
              //_ => panic!(),
              t => return Err(HError::Expected(vec![HLToken::RBrack], t))
            }
            self.advance();
            Ok(HExpr::PartialAltD(Rc::new(wrt), Rc::new(e)))
          }
          HLToken::LBrack => {
            self.advance();
            let e = self.expression(self.lbp(&HLToken::LBrack))?;
            match self.current_token() {
              HLToken::RBrack => {}
              //_ => panic!(),
              t => return Err(HError::Expected(vec![HLToken::RBrack], t))
            }
            self.advance();
            Ok(HExpr::PartialD(Rc::new(e)))
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::Dot, HLToken::LDotCurly, HLToken::LBrack], t))
        }
      }
      /*HLToken::DMinorBrack => {
        self.advance();
        let e = self.expression(self.lbp(&HLToken::LBrack))?;
        match self.current_token() {
          HLToken::RBrack => {}
          _ => panic!(),
        }
        self.advance();
        Ok(HExpr::PartialD(Rc::new(e)))
      }*/
      HLToken::DMinorPrime => {
        unimplemented!();
      }
      HLToken::JMajor => {
        match self.current_token() {
          HLToken::LBrack => {}
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::LBrack], t))
        }
        self.advance();
        let e = self.expression(0)?;
        match self.current_token() {
          HLToken::RBrack => {}
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::RBrack], t))
        }
        self.advance();
        Ok(HExpr::Jacobian(Rc::new(e)))
      }
      HLToken::JMajorPrime => {
        unimplemented!();
      }
      HLToken::Adj => {
        match self.current_token() {
          HLToken::Dyn => {
            self.advance();
            let e = self.expression(0)?;
            Ok(HExpr::AdjDyn(Rc::new(e)))
          }
          _ => {
            let e = self.expression(0)?;
            Ok(HExpr::Adj(Rc::new(e)))
          }
        }
      }
      HLToken::Tng => {
        let e = self.expression(0)?;
        Ok(HExpr::Tng(Rc::new(e)))
      }
      HLToken::Const => {
        let e = self.expression(0)?;
        Ok(HExpr::Const(Rc::new(e)))
      }
      /*HLToken::Pub => {
        match self.current_token() {
          HLToken::Let => {}
          _ => panic!(),
        }
        self.expression(0).map(|e| match e {
          HExpr::Let(decos, lhs, rhs, rest) => {
            let mut decos = decos.unwrap_or_default();
            decos.pub_ = true;
            HExpr::Let(Some(decos), lhs, rhs, rest)
          }
          _ => panic!(),
        })
      }*/
      HLToken::Alt => {
        /*let mut maybe_decos: Option<HLetDecorators> = None;
        loop {
          match self.current_token() {
            HLToken::Rec => {
              let mut decos = maybe_decos.unwrap_or_default();
              decos.rec = true;
              maybe_decos = Some(decos);
              self.advance();
            }
            _ => break,
          }
        }
        panic!();*/
        let e1 = self.expression(0)?;
        match self.current_token() {
          HLToken::In | HLToken::Semi => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::In, HLToken::Semi], t))
        }
        let e2 = self.expression(0)?;
        return Ok(HExpr::Alt_(Rc::new(e1), Rc::new(e2)));
      }
      HLToken::Let => {
        let mut maybe_decos: Option<HLetDecorators> = None;
        loop {
          match self.current_token() {
            /*HLToken::Match => {
              self.advance();
              let pat_e = self.expression(0)?;
              match self.current_token() {
                HLToken::Equals => {}
                _ => panic!(),
              }
              self.advance();
              let query_e = self.expression(0)?;
              match self.current_token() {
                HLToken::In | HLToken::Semi => {}
                _ => panic!(),
              }
              self.advance();
              let rest_e = self.expression(0)?;
              return Ok(HExpr::LetMatch(Rc::new(pat_e), Rc::new(query_e), Rc::new(rest_e)));
            }*/
            HLToken::Alt => {
              let mut decos = maybe_decos.unwrap_or_default();
              decos.alt = true;
              maybe_decos = Some(decos);
              self.advance();
            }
            HLToken::Gen => {
              let mut decos = maybe_decos.unwrap_or_default();
              decos.gen = true;
              maybe_decos = Some(decos);
              self.advance();
            }
            HLToken::Rec => {
              let mut decos = maybe_decos.unwrap_or_default();
              decos.rec = true;
              maybe_decos = Some(decos);
              self.advance();
            }
            /*HLToken::Rnd => {
              let mut decos = maybe_decos.unwrap_or_default();
              decos.rnd = true;
              maybe_decos = Some(decos);
              self.advance();
            }*/
            HLToken::Seq => {
              let mut decos = maybe_decos.unwrap_or_default();
              decos.seq = true;
              maybe_decos = Some(decos);
              self.advance();
            }
            _ => break,
          }
        }
        let decos = maybe_decos.clone().unwrap_or_default();
        if decos.alt {
          let e1_lhs = self.expression(0)?;
          match self.current_token() {
            HLToken::Colon => {
              self.advance();
            }
            //_ => panic!(),
            t => return Err(HError::Expected(vec![HLToken::Colon], t))
          }
          let ty_e = self.expression(0)?;
          let mut decos = maybe_decos.unwrap_or_default();
          decos.ty = Some(Rc::new(ty_e));
          maybe_decos = Some(decos);
          match self.current_token() {
            HLToken::Equals => {
              self.advance();
            }
            //_ => panic!(),
            t => return Err(HError::Expected(vec![HLToken::Equals], t))
          }
          let e1_rhs = self.expression(0)?;
          match self.current_token() {
            HLToken::In | HLToken::Semi => {
              self.advance();
            }
            //_ => panic!(),
            t => return Err(HError::Expected(vec![HLToken::In, HLToken::Semi], t))
          }
          let e2 = self.expression(0)?;
          return Ok(HExpr::Alt(maybe_decos, Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)));
        }
        let e1_lhs = self.expression(0)?;
        match self.current_token() {
          /*HLToken::If => {
            let mut e1_rhs = vec![];
            loop {
              self.advance();
              let e1_rhs0 = self.expression(0)?;
              e1_rhs.push(Rc::new(e1_rhs0));
              match self.current_token() {
                HLToken::Comma => {
                  continue;
                }
                HLToken::In | HLToken::Semi => {
                  break;
                }
                _ => panic!(),
              }
            }
            self.advance();
            let e2 = self.expression(0)?;
            Ok(HExpr::LetIf(Rc::new(e1_lhs), e1_rhs, Rc::new(e2)))
          }
          HLToken::For => {
            // TODO
            let mut e1_unknowns = vec![];
            loop {
              self.advance();
              let e1_unk0 = self.expression(0)?;
              e1_unknowns.push(Rc::new(e1_unk0));
              match self.current_token() {
                HLToken::Comma => {
                  continue;
                }
                HLToken::If => {
                  break;
                }
                _ => panic!(),
              }
            }
            let mut e1_rhs = vec![];
            loop {
              self.advance();
              let e1_rhs0 = self.expression(0)?;
              e1_rhs.push(Rc::new(e1_rhs0));
              match self.current_token() {
                HLToken::Comma => {
                  continue;
                }
                HLToken::In | HLToken::Semi => {
                  break;
                }
                _ => panic!(),
              }
            }
            self.advance();
            let e2 = self.expression(0)?;
            Ok(HExpr::LetForIf(Rc::new(e1_lhs), e1_unknowns, e1_rhs, Rc::new(e2)))
          }
          HLToken::In | HLToken::Semi => {
            self.advance();
            let e2 = self.expression(0)?;
            Ok(HExpr::LetEmpty(Rc::new(e1_lhs), Rc::new(e2)))
          }*/
          HLToken::Colon => {
            // TODO
            self.advance();
            let ty_e = self.expression(0)?;
            /*let mut decos = maybe_decos.unwrap_or_default();
            decos.ty = Some(Rc::new(ty_e));
            maybe_decos = Some(decos);*/
            match self.current_token() {
              HLToken::Equals => {
                self.advance();
                let e1_rhs = self.expression(0)?;
                match self.current_token() {
                  HLToken::In | HLToken::Semi => {
                    self.advance();
                  }
                  //_ => panic!(),
                  t => return Err(HError::Expected(vec![HLToken::In, HLToken::Semi], t))
                }
                let e2 = self.expression(0)?;
                Ok(HExpr::Let(maybe_decos, Some(Rc::new(ty_e)), Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)))
              }
              //_ => panic!(),
              t => return Err(HError::Expected(vec![HLToken::Equals], t))
            }
          }
          HLToken::Equals => {
            self.advance();
            let e1_rhs = self.expression(0)?;
            match self.current_token() {
              HLToken::In | HLToken::Semi => {
                self.advance();
              }
              //_ => panic!(),
              t => return Err(HError::Expected(vec![HLToken::In, HLToken::Semi], t))
            }
            let e2 = self.expression(0)?;
            Ok(HExpr::Let(maybe_decos, None, Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)))
          }
          /*HLToken::Tilde => {
            self.advance();
            let e1_rhs = self.expression(0)?;
            match self.current_token() {
              HLToken::In | HLToken::Semi => {}
              _ => panic!(),
            }
            self.advance();
            let e2 = self.expression(0)?;
            Ok(HExpr::LetRand(Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)))
          }*/
          /*HLToken::Where => {
            let mut e1_clauses = vec![];
            loop {
              self.advance();
              let e1_clause0 = self.expression(0)?;
              e1_clauses.push(Rc::new(e1_clause0));
              match self.current_token() {
                HLToken::Comma => {
                  continue;
                }
                HLToken::Equals => {
                  break;
                }
                _ => panic!(),
              }
            }
            /*self.advance();
            match self.current_token() {
              HLToken::Equals => {}
              _ => panic!(),
            }*/
            self.advance();
            let e1_rhs = self.expression(0)?;
            match self.current_token() {
              HLToken::In | HLToken::Semi => {}
              _ => panic!(),
            }
            self.advance();
            let e2 = self.expression(0)?;
            Ok(HExpr::LetWhere(Rc::new(e1_lhs), e1_clauses, Rc::new(e1_rhs), Rc::new(e2)))
          }*/
          //_ => panic!(),
          tok => panic!("unknown token in let rhs: {:?}", tok),
        }
      }
      /*HLToken::Where => {
        match self.current_token() {
          HLToken::Let => {}
          _ => panic!(),
        }
        self.advance();
        let e1_lhs = self.expression(0)?;
        match self.current_token() {
          HLToken::Equals => {}
          _ => panic!(),
        }
        self.advance();
        let e1_rhs = self.expression(0)?;
        match self.current_token() {
          HLToken::In | HLToken::Semi => {}
          _ => panic!(),
        }
        self.advance();
        let e2 = self.expression(0)?;
        Ok(HExpr::WhereLet(Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)))
      }*/
      HLToken::Switch => {
        let pred_e = self.expression(0)?;
        match self.current_token() {
          HLToken::DashColon => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::DashColon], t))
        }
        let top_e = self.expression(0)?;
        match self.current_token() {
          HLToken::Bar => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::Bar], t))
        }
        let bot_e = self.expression(0)?;
        Ok(HExpr::Switch(Rc::new(pred_e), Rc::new(top_e), Rc::new(bot_e)))
      }
      HLToken::Match => {
        let query_e = self.expression(0)?;
        let mut pat_arms = vec![];
        loop {
          match self.current_token() {
            HLToken::Bar => {
              self.advance();
            }
            _ => break,
          }
          let pat_e = self.expression(0)?;
          match self.current_token() {
            HLToken::RDArrow => {
              self.advance();
            }
            //_ => panic!(),
            t => return Err(HError::Expected(vec![HLToken::RDArrow], t))
          }
          let arm_e = self.expression(0)?;
          pat_arms.push((Rc::new(pat_e), Rc::new(arm_e)));
        }
        if pat_arms.is_empty() {
          //panic!();
          return Err(HError::MissingMatchArms);
        }
        Ok(HExpr::Match(Rc::new(query_e), pat_arms))
      }
      HLToken::Lambda |
      HLToken::Backslash => {
        let mut params = vec![];
        match self.current_token() {
          HLToken::RArrow => {
            self.advance();
          }
          HLToken::PlacePat | HLToken::Ident(_) => {
            loop {
              match self.current_token() {
                HLToken::PlacePat => {
                  unimplemented!();
                }
                HLToken::Ident(param_name) => {
                  // NB: Need to disambiguate between path (dot) lookups and
                  // the terminating dot of a lambda.
                  self.advance();
                  params.push(Rc::new(HExpr::Ident(param_name)));
                  match self.current_token() {
                    HLToken::Comma => {
                      self.advance();
                    }
                    HLToken::RArrow => {
                      self.advance();
                      break;
                    }
                    //_ => panic!(),
                    t => return Err(HError::Expected(vec![HLToken::Comma, HLToken::RArrow], t))
                  }
                }
                //_ => panic!(),
                t => return Err(HError::Expected(vec![HLToken::PlacePat, HLToken::Ident("<identifier>".into())], t))
              }
            }
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::RArrow, HLToken::PlacePat, HLToken::Ident("<identifier>".into())], t))
        }
        let body = self.expression(0)?;
        Ok(HExpr::Lambda(params, Rc::new(body)))
      }
      HLToken::Dash => {
        let right = self.expression(700)?;
        Ok(HExpr::Neg(Rc::new(right)))
      }
      HLToken::LBrack => {
        let mut arg_typats = Vec::new();
        loop {
          match self.current_token() {
            HLToken::RBrack => {
              self.advance();
              break;
            }
            HLToken::BitTy => {
              self.advance();
              arg_typats.push(Rc::new(HTypat::BitTy));
              match self.current_token() {
                HLToken::Comma => {
                  self.advance();
                  continue;
                }
                HLToken::RBrack => {
                  self.advance();
                  break;
                }
                //_ => panic!(),
                t => return Err(HError::Expected(vec![HLToken::Comma, HLToken::RBrack], t))
              }
            }
            HLToken::IntTy => {
              self.advance();
              arg_typats.push(Rc::new(HTypat::IntTy));
              match self.current_token() {
                HLToken::Comma => {
                  self.advance();
                  continue;
                }
                HLToken::RBrack => {
                  self.advance();
                  break;
                }
                //_ => panic!(),
                t => return Err(HError::Expected(vec![HLToken::Comma, HLToken::RBrack], t))
              }
            }
            HLToken::FlpTy => {
              self.advance();
              arg_typats.push(Rc::new(HTypat::FlpTy));
              match self.current_token() {
                HLToken::Comma => {
                  self.advance();
                  continue;
                }
                HLToken::RBrack => {
                  self.advance();
                  break;
                }
                //_ => panic!(),
                t => return Err(HError::Expected(vec![HLToken::Comma, HLToken::RBrack], t))
              }
            }
            HLToken::Ident(name) => {
              self.advance();
              arg_typats.push(Rc::new(HTypat::Ident(name)));
              match self.current_token() {
                HLToken::Comma => {
                  self.advance();
                  continue;
                }
                HLToken::RBrack => {
                  self.advance();
                  break;
                }
                //_ => panic!(),
                t => return Err(HError::Expected(vec![HLToken::Comma, HLToken::RBrack], t))
              }
            }
            HLToken::TyvarIdent(tyvar_name) => {
              self.advance();
              let mut name = tyvar_name.clone();
              name.replace_range(.. 1, "");
              arg_typats.push(Rc::new(HTypat::Tyvar(name)));
              match self.current_token() {
                HLToken::Comma => {
                  self.advance();
                  continue;
                }
                HLToken::RBrack => {
                  self.advance();
                  break;
                }
                //_ => panic!(),
                t => return Err(HError::Expected(vec![HLToken::Comma, HLToken::RBrack], t))
              }
            }
            tok => panic!("TRACE: unhandled token: {:?}", tok),
          }
        }
        match self.current_token() {
          HLToken::RArrow => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::RArrow], t))
        }
        let ret_typat = match self.current_token() {
          HLToken::BitTy => {
            self.advance();
            Rc::new(HTypat::BitTy)
          }
          HLToken::IntTy => {
            self.advance();
            Rc::new(HTypat::IntTy)
          }
          HLToken::FlpTy => {
            self.advance();
            Rc::new(HTypat::FlpTy)
          }
          HLToken::Ident(name) => {
            self.advance();
            Rc::new(HTypat::Ident(name))
          }
          HLToken::TyvarIdent(name) => {
            self.advance();
            Rc::new(HTypat::Tyvar(name))
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![
              HLToken::BitTy,
              HLToken::IntTy,
              HLToken::FlpTy,
              HLToken::Ident("<identifier>".into()),
              HLToken::TyvarIdent("<type-variable>".into()),
          ], t))
        };
        Ok(HExpr::Typat(HTypat::FunTy(arg_typats, ret_typat).into()))
      }
      HLToken::LParenBar => {
        let mut elems = Vec::new();
        match self.current_token() {
          HLToken::RParenBar => {
            self.advance();
            return Ok(HExpr::Tuple(elems));
          }
          _ => {
            loop {
              let right = self.expression(0)?;
              elems.push(Rc::new(right));
              match self.current_token() {
                HLToken::Comma => {
                  self.advance();
                }
                HLToken::RParenBar => {
                  self.advance();
                  return Ok(HExpr::Tuple(elems));
                }
                //_ => panic!(),
                t => return Err(HError::Expected(vec![HLToken::Comma, HLToken::RParenBar], t))
              }
            }
          }
        }
      }
      HLToken::LParen => {
        match self.current_token() {
          HLToken::RParen => {
            self.advance();
            Ok(HExpr::STuple(Vec::new()))
          }
          _ => {
            let right = self.expression(0)?;
            match self.current_token() {
              HLToken::Comma => {
                self.advance();
                let mut elems = vec![Rc::new(right)];
                loop {
                  let right = self.expression(0)?;
                  elems.push(Rc::new(right));
                  match self.current_token() {
                    HLToken::Comma => {
                      self.advance();
                    }
                    HLToken::RParen => {
                      self.advance();
                      assert!(elems.len() >= 2);
                      return Ok(HExpr::STuple(elems));
                    }
                    //_ => panic!(),
                    t => return Err(HError::Expected(vec![HLToken::Comma, HLToken::RParen], t))
                  }
                }
                unreachable!();
              }
              HLToken::RParen => {
                self.advance();
              }
              //_ => panic!(),
              t => return Err(HError::Expected(vec![HLToken::Comma, HLToken::RParen], t))
            }
            Ok(right)
          }
        }
      }
      HLToken::PlacePat => {
        Ok(HExpr::PlacePat)
      }
      HLToken::BitTy => {
        Ok(HExpr::Typat(HTypat::BitTy.into()))
      }
      HLToken::IntTy => {
        Ok(HExpr::Typat(HTypat::IntTy.into()))
      }
      HLToken::FlpTy => {
        Ok(HExpr::Typat(HTypat::FlpTy.into()))
      }
      HLToken::UnitLit => {
        Ok(HExpr::UnitLit)
      }
      /*HLToken::NilSTupLit => {
        Ok(HExpr::NilSTupLit)
      }
      HLToken::NilTupLit => {
        Ok(HExpr::NilTupLit)
      }*/
      HLToken::TeeLit => {
        Ok(HExpr::TeeLit)
      }
      HLToken::BotLit => {
        Ok(HExpr::BotLit)
      }
      HLToken::IntLit(x) => {
        Ok(HExpr::IntLit(x))
      }
      HLToken::FlpLit(x) => {
        Ok(HExpr::FlpLit(x))
      }
      HLToken::Ident(name) => {
        Ok(HExpr::Ident(name))
      }
      HLToken::CrypticIdent(mut name) => {
        name.replace_range(.. 1, "");
        Ok(HExpr::CrypticIdent(name))
      }
      HLToken::UseIdent(mut name) => {
        name.replace_range(.. 1, "");
        Ok(HExpr::UseIdent(name))
      }
      HLToken::TyvarIdent(name) => {
        Ok(HExpr::Typat(HTypat::Tyvar(name).into()))
      }
      _ => {
        Err(HError::Unknown)
      }
    }
  }

  fn led(&mut self, tok: HLToken, left: HExpr) -> Result<HExpr, HError> {
    // TODO
    match tok {
      HLToken::_Eof => {
        Err(HError::Eof)
      }
      /*HLToken::_Err => {
        Err(HError::Other)
      }*/
      HLToken::Dot => {
        match self.current_token() {
          // TODO: finalize the set of terms allowed on RHS.
          HLToken::IntLit(idx) => {
            self.advance();
            if idx < 1 {
              return Err(HError::Other);
            }
            Ok(HExpr::PathIndex(Rc::new(left), idx as _))
          }
          HLToken::Ident(name) => {
            self.advance();
            Ok(HExpr::PathLookup(Rc::new(left), name))
          }
          //_ => panic!(),
          _ => {
            let right = self.expression(self.lbp(&tok))?;
            Ok(HExpr::PathELookup(Rc::new(left), Rc::new(right)))
          }
        }
      }
      HLToken::As => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Alias(Rc::new(left), Rc::new(right)))
      }
      /*HLToken::RArrow => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Arrow(Rc::new(left), Rc::new(right)))
      }*/
      HLToken::PlusPlus => {
        let right = self.expression(self.lbp(&tok) - 1)?;
        Ok(HExpr::Concat(Rc::new(left), Rc::new(right)))
      }
      /*HLToken::ColonColon => {
        let right = self.expression(self.lbp(&tok) - 1)?;
        Ok(HExpr::Cons(Rc::new(left), Rc::new(right)))
      }*/
      HLToken::BarBar => {
        let right = self.expression(self.lbp(&tok) - 1)?;
        Ok(HExpr::ShortOr(Rc::new(left), Rc::new(right)))
      }
      HLToken::HatHat => {
        let right = self.expression(self.lbp(&tok) - 1)?;
        Ok(HExpr::ShortAnd(Rc::new(left), Rc::new(right)))
      }
      HLToken::EqEquals => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Eq(Rc::new(left), Rc::new(right)))
      }
      HLToken::NotEquals => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::NotEq(Rc::new(left), Rc::new(right)))
      }
      HLToken::Gt => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Gt(Rc::new(left), Rc::new(right)))
      }
      HLToken::GtEquals => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::GtEq(Rc::new(left), Rc::new(right)))
      }
      HLToken::Lt => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Lt(Rc::new(left), Rc::new(right)))
      }
      HLToken::LtEquals => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::LtEq(Rc::new(left), Rc::new(right)))
      }
      //HLToken::Bar => {
      /*HLToken::BarBar => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Or(Rc::new(left), Rc::new(right)))
      }*/
      HLToken::Hat => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::And(Rc::new(left), Rc::new(right)))
      }
      HLToken::Plus => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Add(Rc::new(left), Rc::new(right)))
      }
      HLToken::Dash => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Sub(Rc::new(left), Rc::new(right)))
      }
      HLToken::Star => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Mul(Rc::new(left), Rc::new(right)))
      }
      HLToken::Slash => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Div(Rc::new(left), Rc::new(right)))
      }
      HLToken::InfixIdent(ref infix_name) => {
        let mut name = infix_name.clone();
        name.replace_range(.. 1, "");
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Infix(name, Rc::new(left), Rc::new(right)))
      }
      HLToken::LBrack => {
        match self.current_token() {
          HLToken::RBrack => {
            self.advance();
            return Ok(HExpr::Apply(Rc::new(left), vec![]));
          }
          //HLToken::Comma => panic!(),
          HLToken::Comma => return Err(HError::Unexpected(HLToken::Comma)),
          _ => {}
        }
        let right = self.expression(0)?;
        match self.current_token() {
          HLToken::RBrack => {
            self.advance();
            return Ok(HExpr::Apply(Rc::new(left), vec![Rc::new(right)]));
          }
          HLToken::Comma => {
            let mut args = vec![Rc::new(right)];
            loop {
              self.advance();
              let right = self.expression(0)?;
              args.push(Rc::new(right));
              match self.current_token() {
                HLToken::RBrack => {
                  self.advance();
                  assert!(args.len() >= 2);
                  return Ok(HExpr::Apply(Rc::new(left), args));
                }
                HLToken::Comma => {}
                //_ => panic!(),
                t => return Err(HError::Expected(vec![HLToken::RBrack, HLToken::Comma], t))
              }
            }
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::RBrack, HLToken::Comma], t))
        }
      }
      _ => {
        Err(HError::Unknown)
      }
    }
  }

  fn expression(&mut self, rbp: i32) -> Result<HExpr, HError> {
    let mut t = self.current_token();
    self.advance();
    let mut left = self.nud(t)?;
    t = self.current_token();
    while rbp < self.lbp(&t) {
      self.advance();
      left = self.led(t, left)?;
      t = self.current_token();
    }
    Ok(left)
  }

  pub fn parse(mut self) -> Result<Rc<HExpr>, HError> {
    self.advance();
    match self.expression(0) {
      Ok(expr) => Ok(Rc::new(expr)),
      Err(err) => match self.current_token_info() {
        None => {
          println!("TRACE: parse error: {:?}", err);
          Err(err)
        }
        Some(info) => {
          println!("TRACE: parse error at {}:{}: {:?}", info.line_nr + 1, info.line_pos + 1, err);
          Err(err)
        }
      }
    }
  }
}
