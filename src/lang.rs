// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use plex::{lexer};

use std::path::{PathBuf};
use std::rc::{Rc};

lexer! {
  fn next_token(text: 'a) -> HToken;

  r#"\n"#       => HToken::Newline,
  r#"[ \t\r]+"# => HToken::Whitespace,
  r#"--[-]*[ \t]*\|[^\n]*"# => HToken::DocComment,
  r#"--[^\n]*"# => HToken::EolComment,
  r#"\(--(~(.*--\).*))--\)"# => HToken::MultilineComment,

  r#"d'"#       => HToken::DMinorPrime,
  r#"d"#        => HToken::DMinor,
  r#"D'"#       => HToken::DMajorPrime,
  r#"D"#        => HToken::DMajor,
  r#"J'"#       => HToken::JMajorPrime,
  r#"J"#        => HToken::JMajor,
  r#"adj"#      => HToken::Adj,
  r#"alt"#      => HToken::Alt,
  r#"as"#       => HToken::As,
  r#"assert"#   => HToken::Assert,
  r#"break"#    => HToken::Break,
  r#"const"#    => HToken::Const,
  r#"export"#   => HToken::Export,
  r#"def"#      => HToken::Def,
  r#"dyn"#      => HToken::Dyn,
  r#"end"#      => HToken::End,
  r#"for"#      => HToken::For,
  r#"gen"#      => HToken::Gen,
  r#"import"#   => HToken::Import,
  r#"in"#       => HToken::In,
  r#"include"#  => HToken::Include,
  r#"let"#      => HToken::Let,
  r#"match"#    => HToken::Match,
  r#"module"#   => HToken::Module,
  r#"pub"#      => HToken::Pub,
  r#"rec"#      => HToken::Rec,
  r#"ref"#      => HToken::Ref,
  r#"require"#  => HToken::Require,
  r#"return"#   => HToken::Return,
  r#"rnd"#      => HToken::Rnd,
  r#"seq"#      => HToken::Seq,
  r#"switch"#   => HToken::Switch,
  r#"tng"#      => HToken::Tng,
  r#"trace"#    => HToken::Trace,
  r#"type"#     => HToken::Type,
  r#"undef"#    => HToken::Undef,
  r#"unit"#     => HToken::Unit,
  r#"unsafe"#   => HToken::Unsafe,
  r#"where"#    => HToken::Where,
  r#"with"#     => HToken::With,
  r#"λ"#        => HToken::Lambda,
  r#"≤"#        => HToken::LtEquals,
  r#"≥"#        => HToken::GtEquals,
  r#"<="#       => HToken::LtEquals,
  r#"<"#        => HToken::Lt,
  r#">="#       => HToken::GtEquals,
  r#">"#        => HToken::Gt,
  r#"==>"#      => HToken::RDDArrow,
  r#"=>"#       => HToken::RDArrow,
  r#"=="#       => HToken::EqEquals,
  r#"="#        => HToken::Equals,
  r#"\~"#       => HToken::Tilde,
  r#"\\/"#      => HToken::BackslashSlash,
  r#"\\"#       => HToken::Backslash,
  r#"!"#        => HToken::Bang,
  r#"\.\+"#     => HToken::DotPlus,
  r#"\.-"#      => HToken::DotDash,
  r#"\.\*"#     => HToken::DotStar,
  r#"\./"#      => HToken::DotSlash,
  //r#"\.\("#     => HToken::LDotParen,
  //r#"\.\["#     => HToken::LDotBrack,
  //r#"\.\{"#     => HToken::LDotCurly,
  r#"\.\.\."#   => HToken::Ellipsis,
  r#"\.\."#     => HToken::DotDot,
  r#"\."#       => HToken::Dot,
  r#","#        => HToken::Comma,
  r#";;"#       => HToken::SemiSemi,
  r#";"#        => HToken::Semi,
  r#"::"#       => HToken::ColonColon,
  r#":-"#       => HToken::ColonDash,
  r#":="#       => HToken::ColonEquals,
  r#":"#        => HToken::Colon,
  r#"<\|"#      => HToken::LPipe,
  r#"\|>"#      => HToken::RPipe,
  //r#"\|\|"#     => HToken::BarBar,
  r#"\|"#       => HToken::Bar,
  //r#"^^"#       => HToken::HatHat,
  //r#"^"#        => HToken::Hat,
  r#"\+\+"#     => HToken::PlusPlus,
  r#"\+:"#      => HToken::PlusColon,
  r#"\+\."#     => HToken::PlusDot,
  r#"\+"#       => HToken::Plus,
  r#"-o"#       => HToken::ROArrow,
  r#"->"#       => HToken::RArrow,
  r#"-:"#       => HToken::DashColon,
  r#"-\."#      => HToken::DashDot,
  r#"-"#        => HToken::Dash,
  r#"\*:"#      => HToken::StarColon,
  r#"\*\."#     => HToken::StarDot,
  r#"\*\*"#     => HToken::StarStar,
  r#"\*"#       => HToken::Star,
  r#"/\\"#      => HToken::SlashBackslash,
  r#"/:"#       => HToken::SlashColon,
  r#"/\."#      => HToken::SlashDot,
  r#"/="#       => HToken::SlashEquals,
  r#"/"#        => HToken::Slash,
  //r#"\(\|"#     => HToken::LParenBar,
  r#"\(\."#     => HToken::LParenDot,
  r#"\("#       => HToken::LParen,
  //r#"\|\)"#     => HToken::RParenBar,
  r#"\.\)"#     => HToken::RParenDot,
  r#"\)"#       => HToken::RParen,
  r#"\["#       => HToken::LBrack,
  r#"\]"#       => HToken::RBrack,
  r#"\{"#       => HToken::LCurly,
  r#"\}"#       => HToken::RCurly,
  r#"'\["#      => HToken::LQuoteBrack,
  r#"'"#        => HToken::Quote,
  r#"\?_"#      => HToken::StagingPlace,
  r#"\?"#       => HToken::Antiquote,
  r#"[_]+"#     => HToken::Place,

  //r#"'_"#       => HToken::PlaceTy,
  //r#"'\?"#      => HToken::TopTy,
  r#"Quo"#      => HToken::QuoTy,
  r#"Iota"#     => HToken::IotaTy,
  r#"Bit"#      => HToken::BitTy,
  r#"Oct"#      => HToken::OctTy,
  r#"Int"#      => HToken::IntTy,
  r#"Flp"#      => HToken::FlpTy,
  //r#"Flp16"#    => HToken::Flp16Ty,
  //r#"Flp32"#    => HToken::Flp32Ty,
  //r#"Fmp"#      => HToken::FmpTy,

  r#"iota"#     => HToken::Iota,
  r#"tee"#      => HToken::Tee,
  r#"bot"#      => HToken::Bot,
  r#"truth"#    => HToken::Truth,
  r#"false"#    => HToken::False,

  //r#"[0-9]+\.[0-9]*[fp16]"#         => HToken::Flp16Lit(text[ .. text.len() - 1].parse().unwrap()),
  //r#"[0-9]+\.[0-9]*[fp32]"#         => HToken::Flp32Lit(text[ .. text.len() - 1].parse().unwrap()),
  //r#"[0-9]+\.[0-9]*[fmp]"#          => HToken::FmpLit(text[ .. text.len() - 1].parse().unwrap()),
  r#"-[0-9]+\.[0-9]*f"#             => HToken::FlpLit(text[ .. text.len() - 1].parse().unwrap()),
  r#"[0-9]+\.[0-9]*f"#              => HToken::FlpLit(text[ .. text.len() - 1].parse().unwrap()),
  r#"-[0-9]+\.[0-9]*"#              => HToken::FlpLit(text.parse().unwrap()),
  r#"[0-9]+\.[0-9]*"#               => HToken::FlpLit(text.parse().unwrap()),
  r#"-[0-9]+f"#                     => HToken::FlpLit(text[ .. text.len() - 1].parse().unwrap()),
  r#"[0-9]+f"#                      => HToken::FlpLit(text[ .. text.len() - 1].parse().unwrap()),
  r#"-[0-9]+n"#                     => HToken::IntLit(text[ .. text.len() - 1].parse().unwrap()),
  r#"[0-9]+n"#                      => HToken::IntLit(text[ .. text.len() - 1].parse().unwrap()),
  r#"-[0-9]+"#                      => HToken::IntLit(text.parse().unwrap()),
  r#"[0-9]+"#                       => HToken::IntLit(text.parse().unwrap()),

  r#"[a-zA-Z_][a-zA-Z0-9_]*[']*"#   => HToken::Ident(text.to_owned()),
  r#"`[a-zA-Z_][a-zA-Z0-9_]*[']*"#  => HToken::InfixIdent(text.to_owned()),
  r#"^[a-zA-Z_][a-zA-Z0-9_]*[']*"#  => HToken::PostfixIdent(text.to_owned()),
  //r#"'[a-zA-Z_][a-zA-Z0-9_]*[']*"#  => HToken::TyvarIdent(text.to_owned()),
  r#"\?[a-zA-Z_][a-zA-Z0-9_]*"#     => HToken::StagingIdent(text.to_owned()),
  r#"\?[0-9]+"#                     => HToken::StagingIndex(text.to_owned()),
  //r#"\~[A-Za-z0-9/\+]+[=]*"#        => HToken::CrypticIdent(text.to_owned()),
  r#"\~=[A-Za-z0-9/\+]+[=]*"#       => HToken::CrypticIdent(text.to_owned()),
  r#"\~[a-z0-9\-\.]+:[a-z0-9\-/]+"# => HToken::UseIdent(text.to_owned()),
  r#"\~[a-z0-9\-]+"#                => HToken::UseIdent(text.to_owned()),

  r#"."#        => HToken::_Eof,
}

#[derive(Clone, Debug)]
pub enum HError {
  Eof,
  Unknown,
  Reserved(String),
  Unexpected(HToken),
  Expected(Vec<HToken>, HToken),
  ExpectedIntLit,
  ExpectedTypat,
  MissingMatchArms,
  NoGenericAlternative,
  Other,
}

#[derive(Clone, PartialEq, Debug)]
pub enum HToken {
  Newline,
  Whitespace,
  DocComment,
  EolComment,
  MultilineComment,
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
  Alt,
  As,
  Assert,
  Break,
  Const,
  Def,
  Dyn,
  End,
  Export,
  For,
  Gen,
  Import,
  In,
  Include,
  Let,
  Match,
  Module,
  Pub,
  Rec,
  Ref,
  Require,
  Return,
  Rnd,
  Seq,
  Switch,
  Tng,
  Trace,
  Type,
  Undef,
  Unit,
  Unsafe,
  Where,
  With,
  Lambda,
  Equals,
  EqEquals,
  SlashEquals,
  Gt,
  GtEquals,
  Lt,
  LtEquals,
  Tilde,
  Backslash,
  BackslashSlash,
  Bang,
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
  ColonDash,
  ColonEquals,
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
  LPipe,
  RPipe,
  Star,
  StarDot,
  StarColon,
  StarStar,
  Slash,
  SlashDot,
  SlashColon,
  SlashBackslash,
  LDotParen,
  LParenBar,
  RParenBar,
  LParenDot,
  RParenDot,
  LParen,
  RParen,
  LQuoteBrack,
  LDotBrack,
  LBrack,
  RBrack,
  LDotCurly,
  LCurly,
  RCurly,
  Quote,
  Antiquote,
  StagingPlace,
  Place,
  PlaceTy,
  TopTy,
  QuoTy,
  IotaTy,
  BitTy,
  OctTy,
  IntTy,
  FlpTy,
  Iota,
  Tee,
  Bot,
  Truth,
  False,
  IntLit(i64),
  FlpLit(f64),
  Ident(String),
  InfixIdent(String),
  PostfixIdent(String),
  //TyvarIdent(String),
  StagingIdent(String),
  StagingIndex(String),
  CrypticIdent(String),
  UseIdent(String),
  _Eof,
}

#[derive(Clone, Debug)]
pub struct HSourceInfo<'src> {
  pub source:   &'src str,
  pub path:     Option<PathBuf>,
}

#[derive(Clone, Copy, Debug)]
pub struct HTokenInfo {
  pub line_nr:  usize,
  pub line_pos: usize,
  pub span:     Option<(usize, usize)>,
}

#[derive(Clone, Debug)]
pub struct HLexer<'src> {
  source:   &'src str,
  remnant:  &'src str,
  offset:   usize,
  line_nr:  usize,
  line_pos: usize,
  next_pos: usize,
  eof:      bool,
}

impl<'src> HLexer<'src> {
  pub fn new(source: &'src str /*srcinfo: HSourceInfo<'src>*/) -> HLexer<'src> {
    HLexer{
      source,
      remnant:  source,
      offset:   0,
      line_nr:  0,
      line_pos: 0,
      next_pos: 0,
      eof:      false,
    }
  }
}

impl<'src> Iterator for HLexer<'src> {
  type Item = (HToken, HTokenInfo);

  fn next(&mut self) -> Option<(HToken, HTokenInfo)> {
    loop {
      if self.eof {
        let tok_info = HTokenInfo{
          line_nr:    self.line_nr,
          line_pos:   self.line_pos,
          //text:       None,
          span:       None,
        };
        return Some((HToken::_Eof, tok_info));
      }
      let (tok, tok_span, tok_text) = if let Some((tok, tok_text, next_remnant)) = next_token(self.remnant) {
        let tok_start = self.offset;
        let tok_len = tok_text.len();
        let tok_span = (tok_start, tok_start + tok_len);
        self.remnant = next_remnant;
        self.offset += tok_len;
        self.line_pos = self.next_pos;
        self.next_pos += tok_len;
        (tok, Some(tok_span), Some(tok_text))
      } else {
        self.line_pos = self.next_pos;
        self.eof = true;
        (HToken::_Eof, None, None)
      };
      match (tok, tok_span, tok_text) {
        (HToken::Newline, _, _) => {
          self.line_nr += 1;
          self.line_pos = 0;
          self.next_pos = 0;
          continue;
        }
        (HToken::Whitespace, _, _) |
        (HToken::DocComment, _, _) |
        (HToken::EolComment, _, _) => {
          continue;
        }
        (HToken::MultilineComment, _, Some(text)) => {
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
        (HToken::MultilineComment, _, None) => {
          panic!();
        }
        (tok, tok_span, _) => {
          let tok_info = HTokenInfo{
            line_nr:    self.line_nr,
            line_pos:   self.line_pos,
            span:       tok_span,
          };
          return Some((tok, tok_info));
        }
      }
    }
  }
}

#[derive(Clone, PartialEq, Debug, Default)]
pub struct HLetDecorators {
  pub pub_: bool,
  pub alt:  bool,
  pub gen:  bool,
  pub rec:  bool,
  //pub rnd:  bool,
  //pub seq:  bool,
  pub ty:   Option<Rc<HExpr>>,
  //pub ty:   Option<Rc<HTypat>>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum HTypat {
  //Top,
  //Place,
  //Tyvar(String),
  Fun(Vec<Rc<HTypat>>, Rc<HTypat>),
  Quo,
  Iota,
  Bit,
  Oct,
  Int,
  Flp,
  Ident(String),
}

impl From<HToken> for HTypat {
  fn from(tok: HToken) -> HTypat {
    match tok {
      HToken::QuoTy => HTypat::Quo,
      HToken::IotaTy => HTypat::Iota,
      HToken::BitTy => HTypat::Bit,
      HToken::OctTy => HTypat::Oct,
      HToken::IntTy => HTypat::Int,
      HToken::FlpTy => HTypat::Flp,
      HToken::Ident(name) => HTypat::Ident(name),
      _ => panic!(),
    }
  }
}

#[derive(Clone, Debug)]
pub struct HExprRef {
  // FIXME
  pub term: Rc<HExpr>,
  //pub toks: Vec<HTokenInfo>,
}

#[derive(Clone, PartialEq, Debug)]
pub enum HExpr {
  End,
  //Export(Rc<HExpr>, Option<Rc<HExpr>>, Rc<HExpr>),
  //Import(String, Rc<HExpr>),
  Break(Rc<HExpr>),
  Lambda(Vec<Rc<HExpr>>, Rc<HExpr>),
  Apply(Rc<HExpr>, Vec<Rc<HExpr>>),
  Atom(Rc<HExpr>, Vec<Rc<HExpr>>),
  UTuple(Vec<Rc<HExpr>>),
  STuple(Vec<Rc<HExpr>>),
  //ETuple(Vec<Rc<HExpr>>),
  ETuple(Vec<String>),
  PartialD(Rc<HExpr>),
  PartialAltD(Rc<HExpr>, Rc<HExpr>),
  AdjointD(Rc<HExpr>),
  TangentD(Rc<HExpr>),
  //DirectionalD(Rc<HExpr>, Rc<HExpr>),
  Jacobian(Rc<HExpr>),
  JacobianT(Rc<HExpr>),
  Adj(Rc<HExpr>),
  Tng(Rc<HExpr>),
  AdjDyn(Rc<HExpr>),
  Const(Rc<HExpr>),
  Let(Option<HLetDecorators>, Option<Rc<HExpr>>, Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  Alt(Rc<HExpr>, Rc<HExpr>),
  LetAlt(Option<HLetDecorators>, /*Rc<HExpr>,*/ Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
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
  Neg(Rc<HExpr>),
  Defined(Rc<HExpr>),
  Infix(String, Rc<HExpr>, Rc<HExpr>),
  Postfix(String, Rc<HExpr>),
  //Cons(Rc<HExpr>, Rc<HExpr>),
  Concat(Rc<HExpr>, Rc<HExpr>),
  Quote(Rc<HExpr>),
  Antiquote(Rc<HExpr>),
  Place,
  Typat(Rc<HTypat>),
  IotaLit,
  TeeLit,
  BotLit,
  BitLit(bool),
  IntLit(i64),
  FlpLit(f64),
  Ident(String),
  StagingIdent(String),
  StagingIndex(i64),
  CrypticIdent(String),
  UseIdent(String),
  PathIndex(Rc<HExpr>, usize),
  PathLookup(Rc<HExpr>, String),
  PathELookup(Rc<HExpr>, Rc<HExpr>),
  //KeyLookup(Rc<HExpr>, String),
  //Arrow(Rc<HExpr>, Rc<HExpr>),
}

pub struct HParser<Toks> {
  toks: Toks,
  curr: Option<(HToken, HTokenInfo)>,
  prev: Option<(HToken, HTokenInfo)>,
  bt:   bool,
}

impl<Toks: Iterator<Item=(HToken, HTokenInfo)> + Clone> HParser<Toks> {
  pub fn new(toks: Toks) -> HParser<Toks> {
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

  fn current_token_(&self) -> (HToken, Option<HTokenInfo>) {
    if self.bt {
      match self.prev {
        Some((ref tok, ref info)) => (tok.clone(), Some(info.clone())),
        None => (HToken::_Eof, None),
      }
    } else {
      match self.curr {
        Some((ref tok, ref info)) => (tok.clone(), Some(info.clone())),
        None => (HToken::_Eof, None),
      }
    }
  }

  //fn current_token(&mut self) -> (HToken, Option<&'src str>) {
  fn current_token(&self) -> HToken {
    if self.bt {
      match self.prev {
        //Some(ref tok) => tok.clone(),
        Some((ref tok, _)) => tok.clone(),
        None => HToken::_Eof,
      }
    } else {
      match self.curr {
        //Some(ref tok) => tok.clone(),
        Some((ref tok, _)) => tok.clone(),
        None => HToken::_Eof,
      }
    }
  }

  fn current_token_info(&self) -> Option<HTokenInfo> {
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

  fn previous_token_info(&self) -> Option<HTokenInfo> {
    if self.bt {
      panic!();
    } else {
      match self.prev {
        Some((_, ref info)) => Some((*info).clone()),
        None => None,
      }
    }
  }

  fn dash_prefix_rbp(&self) -> i32 {
    540
  }

  fn lbp(&self, tok: &HToken) -> i32 {
    // TODO
    match tok {
      &HToken::End |
      &HToken::Export |
      &HToken::Import |
      &HToken::Module |
      &HToken::Include |
      &HToken::Require |
      &HToken::Break |
      &HToken::Return |
      &HToken::Trace |
      &HToken::DMajor |
      &HToken::DMajorPrime |
      &HToken::DMinor |
      &HToken::DMinorPrime |
      &HToken::JMajor |
      &HToken::JMajorPrime |
      &HToken::Adj |
      &HToken::Tng |
      &HToken::Dyn |
      &HToken::Pub |
      &HToken::Let |
      &HToken::Alt |
      &HToken::Rec |
      &HToken::Rnd |
      &HToken::Seq |
      &HToken::In |
      &HToken::Where |
      &HToken::Switch |
      &HToken::Match |
      &HToken::With |
      &HToken::For |
      &HToken::Lambda |
      &HToken::Equals |
      &HToken::Tilde |
      &HToken::Backslash |
      &HToken::Comma |
      &HToken::SemiSemi |
      &HToken::Semi |
      &HToken::DashColon |
      &HToken::RPipe |
      &HToken::RArrow |
      &HToken::RDArrow |
      &HToken::Colon |
      &HToken::Bar => 0,
      &HToken::ColonColon => 180,
      &HToken::PlusPlus => 200,
      &HToken::BarBar |
      &HToken::BackslashSlash => 300,
      &HToken::HatHat |
      &HToken::SlashBackslash => 320,
      &HToken::EqEquals |
      &HToken::SlashEquals |
      &HToken::Gt |
      &HToken::GtEquals |
      &HToken::Lt |
      &HToken::LtEquals => 400,
      //&HToken::Bar => 460,
      //&HToken::BarBar => 460,
      //&HToken::Hat => 480,
      &HToken::Plus |
      &HToken::Dash => 500,
      &HToken::Star |
      &HToken::Slash => 520,
      &HToken::InfixIdent(_) => 560,
      &HToken::PostfixIdent(_) => 580,
      &HToken::Bang => 600,
      &HToken::As => 780,
      &HToken::Dot => 800,
      //&HToken::LParenBar => _,
      &HToken::RParenBar => 0,
      &HToken::RParenDot => 0,
      &HToken::LParen => 900,
      &HToken::RParen => 0,
      &HToken::LBrack => 900,
      &HToken::RBrack => 0,
      //&HToken::LDotCurly => 800,
      //&HToken::LCurly => _,
      &HToken::RCurly => 0,
      &HToken::Quote => 1000,
      &HToken::_Eof => 0,
      _ => unimplemented!(),
    }
  }

  fn nud(&mut self, tok: HToken, info: Option<HTokenInfo>) -> Result<HExpr, HError> {
    // TODO
    match tok {
      HToken::_Eof => {
        Err(HError::Eof)
      }
      HToken::End => {
        // TODO
        /*let e: HExprRef = HExprRef{
          term: HExpr::End.into(),
          toks: match info {
            None => vec![],
            Some(info) => vec![info],
          }
        };*/
        Ok(HExpr::End)
      }
      HToken::Export => {
        // TODO
        Err(HError::Reserved("export".to_owned()))
      }
      HToken::Import => {
        // TODO
        /*match self.current_token() {
          HToken::Ident(mod_name) => {
            self.advance();
            match self.current_token() {
              HToken::In | HToken::Semi => {}
              _ => panic!(),
            }
            self.advance();
            let e = self.expression(0)?;
            Ok(HExpr::Import(mod_name, Rc::new(e)))
          }
          _ => panic!(),
        }*/
        Err(HError::Reserved("import".to_owned()))
      }
      HToken::DMajor => {
        match self.current_token() {
          HToken::LBrack => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HToken::LBrack], t))
        }
        let e = self.expression(0)?;
        match self.current_token() {
          /*HToken::Semi => {
            self.advance();
            let dir_e = self.expression(0)?;
            match self.current_token() {
              HToken::RBrack => {
                self.advance();
              }
              _ => panic!(),
            }
            return Ok(HExpr::DirectionalD(Rc::new(e), Rc::new(dir_e)));
          }*/
          HToken::RBrack => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HToken::RBrack], t))
        }
        Ok(HExpr::AdjointD(Rc::new(e)))
      }
      HToken::DMajorPrime => {
        match self.current_token() {
          HToken::LBrack => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HToken::LBrack], t))
        }
        let e = self.expression(0)?;
        match self.current_token() {
          HToken::RBrack => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HToken::RBrack], t))
        }
        Ok(HExpr::TangentD(Rc::new(e)))
      }
      HToken::DMinor => {
        match self.current_token() {
          HToken::Dot => {
            self.advance();
            let mut idents = Vec::new();
            match self.current_token() {
              HToken::LCurly => {
                self.advance();
                match self.current_token() {
                  HToken::RCurly => {
                    self.advance();
                  }
                  _ => {
                    loop {
                      match self.current_token() {
                        HToken::Ident(ident) => {
                          self.advance();
                          idents.push(ident);
                        }
                        t => return Err(HError::Expected(vec![HToken::Ident("<identifier>".to_owned())], t))
                      }
                      match self.current_token() {
                        HToken::Comma => {
                          self.advance();
                        }
                        HToken::RCurly => {
                          self.advance();
                          break;
                        }
                        //_ => panic!(),
                        t => return Err(HError::Expected(vec![HToken::Comma, HToken::RCurly], t))
                      }
                    }
                  }
                }
              }
              HToken::Ident(ident) => {
                self.advance();
                idents.push(ident);
              }
              t => return Err(HError::Expected(vec![HToken::LCurly, HToken::Ident("<identifier>".to_owned())], t))
            }
            let wrt = HExpr::ETuple(idents);
            match self.current_token() {
              HToken::LBrack => {
                self.advance();
              }
              t => return Err(HError::Expected(vec![HToken::LBrack], t))
            }
            let e = self.expression(0)?;
            match self.current_token() {
              HToken::RBrack => {
                self.advance();
              }
              t => return Err(HError::Expected(vec![HToken::RBrack], t))
            }
            Ok(HExpr::PartialAltD(Rc::new(wrt), Rc::new(e)))
          }
          /*HToken::LDotCurly => {
            self.advance();
            let mut idents = Vec::new();
            match self.current_token() {
              HToken::RCurly => {
                self.advance();
              }
              _ => {
                loop {
                  let e = self.expression(0)?;
                  idents.push(Rc::new(e));
                  match self.current_token() {
                    HToken::Comma => {
                      self.advance();
                    }
                    HToken::RCurly => {
                      self.advance();
                      break;
                    }
                    //_ => panic!(),
                    t => return Err(HError::Expected(vec![HToken::Comma, HToken::RCurly], t))
                  }
                }
              }
            }
            let wrt = HExpr::ETuple(idents);
            match self.current_token() {
              HToken::LBrack => {
                self.advance();
              }
              //_ => panic!(),
              t => return Err(HError::Expected(vec![HToken::LBrack], t))
            }
            let e = self.expression(0)?;
            match self.current_token() {
              HToken::RBrack => {
                self.advance();
              }
              //_ => panic!(),
              t => return Err(HError::Expected(vec![HToken::RBrack], t))
            }
            Ok(HExpr::PartialAltD(Rc::new(wrt), Rc::new(e)))
          }*/
          HToken::LBrack => {
            self.advance();
            let e = self.expression(self.lbp(&HToken::LBrack))?;
            match self.current_token() {
              HToken::RBrack => {
                self.advance();
              }
              //_ => panic!(),
              t => return Err(HError::Expected(vec![HToken::RBrack], t))
            }
            Ok(HExpr::PartialD(Rc::new(e)))
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HToken::Dot, HToken::LDotCurly, HToken::LBrack], t))
        }
      }
      /*HToken::DMinorBrack => {
        self.advance();
        let e = self.expression(self.lbp(&HToken::LBrack))?;
        match self.current_token() {
          HToken::RBrack => {}
          _ => panic!(),
        }
        self.advance();
        Ok(HExpr::PartialD(Rc::new(e)))
      }*/
      HToken::DMinorPrime => {
        Err(HError::Reserved("d'".to_owned()))
      }
      HToken::JMajor => {
        match self.current_token() {
          HToken::LBrack => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HToken::LBrack], t))
        }
        let e = self.expression(0)?;
        match self.current_token() {
          HToken::RBrack => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HToken::RBrack], t))
        }
        Ok(HExpr::Jacobian(Rc::new(e)))
      }
      HToken::JMajorPrime => {
        match self.current_token() {
          HToken::LBrack => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HToken::LBrack], t))
        }
        let e = self.expression(0)?;
        match self.current_token() {
          HToken::RBrack => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HToken::RBrack], t))
        }
        Ok(HExpr::JacobianT(Rc::new(e)))
      }
      /*HToken::Adj => {
        match self.current_token() {
          HToken::Dyn => {
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
      HToken::Tng => {
        let e = self.expression(0)?;
        Ok(HExpr::Tng(Rc::new(e)))
      }*/
      HToken::Const => {
        let e = self.expression(0)?;
        Ok(HExpr::Const(Rc::new(e)))
      }
      /*HToken::Pub => {
        match self.current_token() {
          HToken::Let => {}
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
      HToken::Alt => {
        let e1 = self.expression(0)?;
        match self.current_token() {
          HToken::In | HToken::Semi => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HToken::In, HToken::Semi], t))
        }
        let e2 = self.expression(0)?;
        return Ok(HExpr::Alt(Rc::new(e1), Rc::new(e2)));
      }
      HToken::Let => {
        let mut maybe_decos: Option<HLetDecorators> = None;
        loop {
          match self.current_token() {
            /*HToken::Match => {
              self.advance();
              let pat_e = self.expression(0)?;
              match self.current_token() {
                HToken::Equals => {}
                _ => panic!(),
              }
              self.advance();
              let query_e = self.expression(0)?;
              match self.current_token() {
                HToken::In | HToken::Semi => {}
                _ => panic!(),
              }
              self.advance();
              let rest_e = self.expression(0)?;
              return Ok(HExpr::LetMatch(Rc::new(pat_e), Rc::new(query_e), Rc::new(rest_e)));
            }*/
            HToken::Alt => {
              let mut decos = maybe_decos.unwrap_or_default();
              decos.alt = true;
              maybe_decos = Some(decos);
              self.advance();
            }
            HToken::Gen => {
              let mut decos = maybe_decos.unwrap_or_default();
              decos.gen = true;
              maybe_decos = Some(decos);
              self.advance();
            }
            HToken::Rec => {
              let mut decos = maybe_decos.unwrap_or_default();
              decos.rec = true;
              maybe_decos = Some(decos);
              self.advance();
            }
            /*HToken::Rnd => {
              let mut decos = maybe_decos.unwrap_or_default();
              decos.rnd = true;
              maybe_decos = Some(decos);
              self.advance();
            }*/
            /*HToken::Seq => {
              let mut decos = maybe_decos.unwrap_or_default();
              decos.seq = true;
              maybe_decos = Some(decos);
              self.advance();
            }*/
            _ => break,
          }
        }
        let decos = maybe_decos.clone().unwrap_or_default();
        if decos.gen {
          return Err(HError::Reserved("let gen".to_owned()));
        }
        if decos.alt {
          if decos.gen {
            return Err(HError::NoGenericAlternative);
          }
          let e1_lhs = self.expression(0)?;
          match self.current_token() {
            HToken::Colon => {
              self.advance();
            }
            //_ => panic!(),
            t => return Err(HError::Expected(vec![HToken::Colon], t))
          }
          let ty_e = self.expression(0)?;
          let mut decos = maybe_decos.unwrap_or_default();
          decos.ty = Some(Rc::new(ty_e));
          maybe_decos = Some(decos);
          match self.current_token() {
            HToken::Equals => {
              self.advance();
            }
            //_ => panic!(),
            t => return Err(HError::Expected(vec![HToken::Equals], t))
          }
          let e1_rhs = self.expression(0)?;
          match self.current_token() {
            HToken::In | HToken::Semi => {
              self.advance();
            }
            //_ => panic!(),
            t => return Err(HError::Expected(vec![HToken::In, HToken::Semi], t))
          }
          let e2 = self.expression(0)?;
          return Ok(HExpr::LetAlt(maybe_decos, Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)));
        }
        let e1_lhs = self.expression(0)?;
        match self.current_token() {
          /*HToken::If => {
            let mut e1_rhs = vec![];
            loop {
              self.advance();
              let e1_rhs0 = self.expression(0)?;
              e1_rhs.push(Rc::new(e1_rhs0));
              match self.current_token() {
                HToken::Comma => {
                  continue;
                }
                HToken::In | HToken::Semi => {
                  break;
                }
                _ => panic!(),
              }
            }
            self.advance();
            let e2 = self.expression(0)?;
            Ok(HExpr::LetIf(Rc::new(e1_lhs), e1_rhs, Rc::new(e2)))
          }
          HToken::For => {
            // TODO
            let mut e1_unknowns = vec![];
            loop {
              self.advance();
              let e1_unk0 = self.expression(0)?;
              e1_unknowns.push(Rc::new(e1_unk0));
              match self.current_token() {
                HToken::Comma => {
                  continue;
                }
                HToken::If => {
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
                HToken::Comma => {
                  continue;
                }
                HToken::In | HToken::Semi => {
                  break;
                }
                _ => panic!(),
              }
            }
            self.advance();
            let e2 = self.expression(0)?;
            Ok(HExpr::LetForIf(Rc::new(e1_lhs), e1_unknowns, e1_rhs, Rc::new(e2)))
          }
          HToken::In | HToken::Semi => {
            self.advance();
            let e2 = self.expression(0)?;
            Ok(HExpr::LetEmpty(Rc::new(e1_lhs), Rc::new(e2)))
          }*/
          HToken::Colon => {
            // TODO
            self.advance();
            let ty_e = self.expression(0)?;
            /*let mut decos = maybe_decos.unwrap_or_default();
            decos.ty = Some(Rc::new(ty_e));
            maybe_decos = Some(decos);*/
            match self.current_token() {
              HToken::Equals => {
                self.advance();
                let e1_rhs = self.expression(0)?;
                match self.current_token() {
                  HToken::In | HToken::Semi => {
                    self.advance();
                  }
                  //_ => panic!(),
                  t => return Err(HError::Expected(vec![HToken::In, HToken::Semi], t))
                }
                let e2 = self.expression(0)?;
                Ok(HExpr::Let(maybe_decos, Some(Rc::new(ty_e)), Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)))
              }
              //_ => panic!(),
              t => return Err(HError::Expected(vec![HToken::Equals], t))
            }
          }
          HToken::Equals => {
            self.advance();
            let e1_rhs = self.expression(0)?;
            match self.current_token() {
              HToken::In | HToken::Semi => {
                self.advance();
              }
              //_ => panic!(),
              t => return Err(HError::Expected(vec![HToken::In, HToken::Semi], t))
            }
            let e2 = self.expression(0)?;
            Ok(HExpr::Let(maybe_decos, None, Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)))
          }
          /*HToken::Tilde => {
            self.advance();
            let e1_rhs = self.expression(0)?;
            match self.current_token() {
              HToken::In | HToken::Semi => {}
              _ => panic!(),
            }
            self.advance();
            let e2 = self.expression(0)?;
            Ok(HExpr::LetRand(Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)))
          }*/
          /*HToken::Where => {
            let mut e1_clauses = vec![];
            loop {
              self.advance();
              let e1_clause0 = self.expression(0)?;
              e1_clauses.push(Rc::new(e1_clause0));
              match self.current_token() {
                HToken::Comma => {
                  continue;
                }
                HToken::Equals => {
                  break;
                }
                _ => panic!(),
              }
            }
            /*self.advance();
            match self.current_token() {
              HToken::Equals => {}
              _ => panic!(),
            }*/
            self.advance();
            let e1_rhs = self.expression(0)?;
            match self.current_token() {
              HToken::In | HToken::Semi => {}
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
      /*HToken::Where => {
        match self.current_token() {
          HToken::Let => {}
          _ => panic!(),
        }
        self.advance();
        let e1_lhs = self.expression(0)?;
        match self.current_token() {
          HToken::Equals => {}
          _ => panic!(),
        }
        self.advance();
        let e1_rhs = self.expression(0)?;
        match self.current_token() {
          HToken::In | HToken::Semi => {}
          _ => panic!(),
        }
        self.advance();
        let e2 = self.expression(0)?;
        Ok(HExpr::WhereLet(Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)))
      }*/
      HToken::Switch => {
        let pred_e = self.expression(0)?;
        match self.current_token() {
          HToken::DashColon => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HToken::DashColon], t))
        }
        let top_e = self.expression(0)?;
        match self.current_token() {
          HToken::Bar => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HToken::Bar], t))
        }
        let bot_e = self.expression(0)?;
        Ok(HExpr::Switch(Rc::new(pred_e), Rc::new(top_e), Rc::new(bot_e)))
      }
      HToken::Match => {
        let query_e = self.expression(0)?;
        match self.current_token() {
          HToken::With => {
            self.advance();
          }
          t => return Err(HError::Expected(vec![HToken::With], t))
        }
        let mut pat_arms = vec![];
        loop {
          match self.current_token() {
            HToken::Bar => {
              self.advance();
            }
            _ => break,
          }
          let pat_e = self.expression(0)?;
          match self.current_token() {
            HToken::RDArrow => {
              self.advance();
            }
            t => return Err(HError::Expected(vec![HToken::RDArrow], t))
          }
          let arm_e = self.expression(0)?;
          pat_arms.push((Rc::new(pat_e), Rc::new(arm_e)));
        }
        if pat_arms.is_empty() {
          return Err(HError::MissingMatchArms);
        }
        Ok(HExpr::Match(Rc::new(query_e), pat_arms))
      }
      HToken::Lambda |
      HToken::Backslash => {
        let mut params = vec![];
        match self.current_token() {
          HToken::RArrow => {
            self.advance();
          }
          HToken::Place | HToken::Ident(_) => {
            loop {
              match self.current_token() {
                HToken::Place => {
                  self.advance();
                  params.push(Rc::new(HExpr::Place));
                }
                HToken::Ident(param_name) => {
                  self.advance();
                  params.push(Rc::new(HExpr::Ident(param_name)));
                }
                //_ => panic!(),
                t => return Err(HError::Expected(vec![HToken::Place, HToken::Ident("<identifier>".into())], t))
              }
              match self.current_token() {
                HToken::Comma => {
                  self.advance();
                }
                HToken::RArrow => {
                  self.advance();
                  break;
                }
                //_ => panic!(),
                t => return Err(HError::Expected(vec![HToken::Comma, HToken::RArrow], t))
              }
            }
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HToken::RArrow, HToken::Place, HToken::Ident("<identifier>".into())], t))
        }
        let body = self.expression(0)?;
        Ok(HExpr::Lambda(params, Rc::new(body)))
      }
      HToken::Dash => {
        let right = self.expression(self.dash_prefix_rbp())?;
        Ok(HExpr::Neg(Rc::new(right)))
      }
      HToken::LBrack => {
        let mut arg_typats = Vec::new();
        loop {
          let arg_tok = self.current_token();
          match &arg_tok {
            &HToken::LBrack => {
              let arg_e = self.expression(0)?;
              match arg_e {
                HExpr::Typat(arg_ty) => match &*arg_ty {
                  &HTypat::Fun(..) => {
                    arg_typats.push(arg_ty);
                  }
                  _ => panic!(),
                },
                _ => return Err(HError::ExpectedTypat)
              }
            }
            &HToken::RBrack => {
              self.advance();
              break;
            }
            &HToken::QuoTy |
            &HToken::IotaTy |
            &HToken::BitTy |
            &HToken::OctTy |
            &HToken::IntTy |
            &HToken::FlpTy |
            &HToken::Ident(_) => {
              self.advance();
              arg_typats.push(HTypat::from(arg_tok).into());
              match self.current_token() {
                HToken::Comma => {
                  self.advance();
                  continue;
                }
                HToken::RBrack => {
                  self.advance();
                  break;
                }
                t => return Err(HError::Expected(vec![HToken::Comma, HToken::RBrack], t))
              }
            }
            //_ => panic!("TRACE: not a type pattern: {:?}", arg_tok),
            _ => return Err(HError::Expected(vec![
                HToken::LBrack,
                HToken::RBrack,
                HToken::QuoTy,
                HToken::IotaTy,
                HToken::BitTy,
                HToken::OctTy,
                HToken::IntTy,
                HToken::FlpTy,
                HToken::Ident("<identifier>".into()),
                //HToken::TyvarIdent("<type-variable>".into()),
            ], tok))
          }
        }
        match self.current_token() {
          HToken::RArrow => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HToken::RArrow], t))
        }
        let ret_tok = self.current_token();
        let ret_typat = match &ret_tok {
          &HToken::LBrack => {
            let ret_e = self.expression(0)?;
            match ret_e {
              HExpr::Typat(ret_ty) => match &*ret_ty {
                &HTypat::Fun(..) => ret_ty,
                _ => panic!(),
              },
              _ => return Err(HError::ExpectedTypat)
            }
          }
          &HToken::QuoTy |
          &HToken::IotaTy |
          &HToken::BitTy |
          &HToken::OctTy |
          &HToken::IntTy |
          &HToken::FlpTy |
          &HToken::Ident(_) => {
            self.advance();
            HTypat::from(ret_tok).into()
          }
          //_ => panic!(),
          _ => return Err(HError::Expected(vec![
              HToken::LBrack,
              HToken::QuoTy,
              HToken::IotaTy,
              HToken::BitTy,
              HToken::OctTy,
              HToken::IntTy,
              HToken::FlpTy,
              HToken::Ident("<identifier>".into()),
              //HToken::TyvarIdent("<type-variable>".into()),
          ], tok))
        };
        Ok(HExpr::Typat(HTypat::Fun(arg_typats, ret_typat).into()))
      }
      //HToken::LParenBar => {
      HToken::LParenDot => {
        let mut elems = Vec::new();
        match self.current_token() {
          //HToken::RParenBar => {
          HToken::RParenDot => {
            self.advance();
            return Ok(HExpr::UTuple(elems));
          }
          _ => {
            loop {
              let right = self.expression(0)?;
              elems.push(Rc::new(right));
              match self.current_token() {
                HToken::Comma => {
                  self.advance();
                }
                //HToken::RParenBar => {
                HToken::RParenDot => {
                  self.advance();
                  return Ok(HExpr::UTuple(elems));
                }
                //_ => panic!(),
                //t => return Err(HError::Expected(vec![HToken::Comma, HToken::RParenBar], t))
                t => return Err(HError::Expected(vec![HToken::Comma, HToken::RParenDot], t))
              }
            }
          }
        }
      }
      HToken::LParen => {
        match self.current_token() {
          HToken::RParen => {
            self.advance();
            Ok(HExpr::STuple(Vec::new()))
          }
          _ => {
            let right = self.expression(0)?;
            match self.current_token() {
              HToken::Comma => {
                let mut elems = vec![Rc::new(right)];
                loop {
                  match self.current_token() {
                    HToken::Comma => {
                      self.advance();
                    }
                    HToken::RParen => {
                      self.advance();
                      assert!(elems.len() >= 2);
                      return Ok(HExpr::STuple(elems));
                    }
                    t => return Err(HError::Expected(vec![HToken::Comma, HToken::RParen], t))
                  }
                  match self.current_token() {
                    HToken::Comma => return Err(HError::Unexpected(HToken::Comma)),
                    HToken::RParen => {
                      self.advance();
                      return Ok(HExpr::STuple(elems));
                    }
                    _ => {}
                  }
                  let right = self.expression(0)?;
                  elems.push(Rc::new(right));
                }
              }
              HToken::RParen => {
                self.advance();
              }
              t => return Err(HError::Expected(vec![HToken::Comma, HToken::RParen], t))
            }
            Ok(right)
          }
        }
      }
      HToken::Quote => {
        let e = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Quote(e.into()))
      }
      HToken::Antiquote => {
        match self.current_token() {
          HToken::LParen => {
            self.advance();
          }
          t => return Err(HError::Expected(vec![HToken::LParen], t))
        }
        let e = self.expression(0)?;
        match self.current_token() {
          HToken::RParen => {
            self.advance();
          }
          t => return Err(HError::Expected(vec![HToken::RParen], t))
        }
        Ok(HExpr::Antiquote(e.into()))
      }
      HToken::Place => {
        Ok(HExpr::Place)
      }
      HToken::QuoTy |
      HToken::IotaTy |
      HToken::BitTy |
      HToken::OctTy |
      HToken::IntTy |
      HToken::FlpTy => {
        Ok(HExpr::Typat(HTypat::from(tok).into()))
      }
      HToken::Iota => {
        Ok(HExpr::IotaLit)
      }
      HToken::Tee => {
        Ok(HExpr::TeeLit)
      }
      HToken::Bot => {
        Ok(HExpr::BotLit)
      }
      HToken::Truth => {
        Ok(HExpr::BitLit(true))
      }
      HToken::False => {
        Ok(HExpr::BitLit(false))
      }
      HToken::IntLit(x) => {
        match self.current_token() {
          HToken::Ident(name) => {
            // FIXME
            return Err(HError::Reserved("dimensional literals".to_owned()));
          }
          _ => {}
        }
        Ok(HExpr::IntLit(x))
      }
      HToken::FlpLit(x) => {
        match self.current_token() {
          HToken::Ident(name) => {
            // FIXME
            return Err(HError::Reserved("dimensional literals".to_owned()));
          }
          _ => {}
        }
        Ok(HExpr::FlpLit(x))
      }
      HToken::Ident(name) => {
        Ok(HExpr::Ident(name))
      }
      /*HToken::TyvarIdent(name) => {
        Ok(HExpr::Typat(HTypat::Tyvar(name).into()))
      }*/
      HToken::StagingIdent(mut name) => {
        name.replace_range(.. 1, "");
        Ok(HExpr::StagingIdent(name))
      }
      HToken::StagingIndex(mut name) => {
        name.replace_range(.. 1, "");
        Ok(HExpr::StagingIndex(name.parse().map_err(|_| HError::ExpectedIntLit)?))
      }
      HToken::CrypticIdent(mut name) => {
        name.replace_range(.. 1, "");
        Ok(HExpr::CrypticIdent(name))
      }
      HToken::UseIdent(mut name) => {
        name.replace_range(.. 1, "");
        Ok(HExpr::UseIdent(name))
      }
      _ => {
        Err(HError::Unknown)
      }
    }
  }

  fn led(&mut self, tok: HToken, left: HExpr) -> Result<HExpr, HError> {
    // TODO
    match tok {
      HToken::_Eof => {
        Err(HError::Eof)
      }
      HToken::Dot => {
        match self.current_token() {
          // TODO: finalize the set of terms allowed on RHS.
          HToken::IntLit(idx) => {
            self.advance();
            if idx < 1 {
              return Err(HError::Other);
            }
            Ok(HExpr::PathIndex(Rc::new(left), idx as _))
          }
          HToken::Ident(name) => {
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
      HToken::As => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Alias(Rc::new(left), Rc::new(right)))
      }
      /*HToken::RArrow => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Arrow(Rc::new(left), Rc::new(right)))
      }*/
      HToken::PlusPlus => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Concat(Rc::new(left), Rc::new(right)))
      }
      /*HToken::ColonColon => {
        let right = self.expression(self.lbp(&tok) - 1)?;
        Ok(HExpr::Cons(Rc::new(left), Rc::new(right)))
      }*/
      //HToken::BarBar |
      HToken::BackslashSlash => {
        let right = self.expression(self.lbp(&tok) - 1)?;
        Ok(HExpr::ShortOr(Rc::new(left), Rc::new(right)))
      }
      //HToken::HatHat |
      HToken::SlashBackslash => {
        let right = self.expression(self.lbp(&tok) - 1)?;
        Ok(HExpr::ShortAnd(Rc::new(left), Rc::new(right)))
      }
      HToken::EqEquals => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Eq(Rc::new(left), Rc::new(right)))
      }
      HToken::SlashEquals => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::NotEq(Rc::new(left), Rc::new(right)))
      }
      HToken::Gt => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Gt(Rc::new(left), Rc::new(right)))
      }
      HToken::GtEquals => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::GtEq(Rc::new(left), Rc::new(right)))
      }
      HToken::Lt => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Lt(Rc::new(left), Rc::new(right)))
      }
      HToken::LtEquals => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::LtEq(Rc::new(left), Rc::new(right)))
      }
      /*//HToken::Bar => {
      HToken::BarBar => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Or(Rc::new(left), Rc::new(right)))
      }
      HToken::Hat => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::And(Rc::new(left), Rc::new(right)))
      }*/
      HToken::Plus => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Add(Rc::new(left), Rc::new(right)))
      }
      HToken::Dash => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Sub(Rc::new(left), Rc::new(right)))
      }
      HToken::Star => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Mul(Rc::new(left), Rc::new(right)))
      }
      HToken::Slash => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Div(Rc::new(left), Rc::new(right)))
      }
      HToken::InfixIdent(ref infix_name) => {
        let mut name = infix_name.clone();
        name.replace_range(.. 1, "");
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Infix(name, Rc::new(left), Rc::new(right)))
      }
      HToken::PostfixIdent(ref postfix_name) => {
        let mut name = postfix_name.clone();
        name.replace_range(.. 1, "");
        Ok(HExpr::Postfix(name, Rc::new(left)))
      }
      HToken::Bang => {
        Ok(HExpr::Defined(Rc::new(left)))
      }
      HToken::LParen => {
        let mut args = Vec::with_capacity(1);
        loop {
          match self.current_token() {
            HToken::RParen => {
              self.advance();
              return Ok(HExpr::Atom(Rc::new(left), args));
            }
            HToken::Comma => return Err(HError::Unexpected(HToken::Comma)),
            _ => {}
          }
          let right = self.expression(0)?;
          args.push(right.into());
          match self.current_token() {
            HToken::RParen => {
              self.advance();
              assert!(args.len() >= 2);
              return Ok(HExpr::Atom(left.into(), args));
            }
            HToken::Comma => {
              self.advance();
            }
            t => return Err(HError::Expected(vec![HToken::RParen, HToken::Comma], t))
          }
        }
      }
      HToken::LBrack => {
        match self.current_token() {
          HToken::RBrack => {
            self.advance();
            return Ok(HExpr::Apply(Rc::new(left), vec![]));
          }
          //HToken::Comma => panic!(),
          HToken::Comma => return Err(HError::Unexpected(HToken::Comma)),
          _ => {}
        }
        let right = self.expression(0)?;
        match self.current_token() {
          HToken::RBrack => {
            self.advance();
            return Ok(HExpr::Apply(Rc::new(left), vec![Rc::new(right)]));
          }
          HToken::Comma => {
            let mut args = vec![Rc::new(right)];
            loop {
              self.advance();
              let right = self.expression(0)?;
              args.push(Rc::new(right));
              match self.current_token() {
                HToken::RBrack => {
                  self.advance();
                  assert!(args.len() >= 2);
                  return Ok(HExpr::Apply(Rc::new(left), args));
                }
                HToken::Comma => {}
                //_ => panic!(),
                t => return Err(HError::Expected(vec![HToken::RBrack, HToken::Comma], t))
              }
            }
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HToken::RBrack, HToken::Comma], t))
        }
      }
      _ => {
        Err(HError::Unknown)
      }
    }
  }

  fn expression(&mut self, rbp: i32) -> Result<HExpr, HError> {
    let (mut t, tinfo) = self.current_token_();
    self.advance();
    let mut left = self.nud(t, tinfo)?;
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
      Err(err) => match self.previous_token_info() {
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
