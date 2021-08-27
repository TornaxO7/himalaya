use clap;

use crate::{
    config::model::{Account, Config},
    output::model::Output,
};

/// `Ctx` stands for `Context` and includes the most "important" structs which are used quite often
/// in this crate.
#[derive(Debug, Default, Clone)]
pub struct Ctx<'a> {
    pub config: Config,
    pub account: Account,
    pub output: Output,
    pub mbox: String,
    pub arg_matches: clap::ArgMatches<'a>,
}

impl<'a> Ctx<'a> {
    pub fn new<S: ToString>(
        config: Config,
        account: Account,
        output: Output,
        mbox: S,
        arg_matches: clap::ArgMatches<'a>,
    ) -> Self {
        let mbox = mbox.to_string();

        Self {
            config,
            account,
            output,
            mbox,
            arg_matches,
        }
    }
}
