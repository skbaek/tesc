use::std::env;
use tptp::parsers::TPTPIterator;
use tptp::syntax::*;

mod basic;
use basic::*;

fn main() -> Rst<()> {
  let args: Vec<String> = env::args().collect();
  let tptp = &args[1];
  
  let bytes = to_boxed_slice(tptp)?;
  let mut is = TPTPIterator::<()>::new(&bytes);


  Ok(())
}
