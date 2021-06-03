use error_chain::error_chain;
use lettre::transport::smtp::authentication::Credentials as SmtpCredentials;
use log::debug;
use serde::Deserialize;
use std::{
    collections::HashMap,
    env,
    fs::{self, File},
    io::Read,
    path::PathBuf,
    thread,
};
use toml;

use crate::output::utils::run_cmd;

use super::tui::TuiConfig;

error_chain! {}

const DEFAULT_PAGE_SIZE: usize = 10;

/// # Account
/// This struct represents the data of an account. For more information, please
/// take a look into its [wiki
/// page](https://github.com/soywod/himalaya/wiki/Configuration:config-file#account-specific-settings).
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub struct Account {
    // Override
    pub name: Option<String>,
    pub downloads_dir: Option<PathBuf>,
    pub signature: Option<String>,
    pub default_page_size: Option<usize>,
    pub watch_cmds: Option<Vec<String>>,

    // Specific
    pub default: Option<bool>,
    pub email: String,

    pub imap_host: String,
    pub imap_port: u16,
    pub imap_starttls: Option<bool>,
    pub imap_insecure: Option<bool>,
    pub imap_login: String,
    pub imap_passwd_cmd: String,

    pub smtp_host: String,
    pub smtp_port: u16,
    pub smtp_starttls: Option<bool>,
    pub smtp_insecure: Option<bool>,
    pub smtp_login: String,
    pub smtp_passwd_cmd: String,
}

impl Account {
    pub fn imap_addr(&self) -> (&str, u16) {
        debug!("host: {}", self.imap_host);
        debug!("port: {}", self.imap_port);
        (&self.imap_host, self.imap_port)
    }

    pub fn imap_passwd(&self) -> Result<String> {
        let passwd = run_cmd(&self.imap_passwd_cmd).chain_err(|| "Cannot run IMAP passwd cmd")?;
        let passwd = passwd
            .trim_end_matches(|c| c == '\r' || c == '\n')
            .to_owned();

        Ok(passwd)
    }

    pub fn imap_starttls(&self) -> bool {
        let starttls = match self.imap_starttls {
            Some(true) => true,
            _ => false,
        };

        debug!("STARTTLS: {}", starttls);
        starttls
    }

    pub fn imap_insecure(&self) -> bool {
        let insecure = match self.imap_insecure {
            Some(true) => true,
            _ => false,
        };

        debug!("insecure: {}", insecure);
        insecure
    }

    pub fn smtp_creds(&self) -> Result<SmtpCredentials> {
        let passwd = run_cmd(&self.smtp_passwd_cmd).chain_err(|| "Cannot run SMTP passwd cmd")?;
        let passwd = passwd
            .trim_end_matches(|c| c == '\r' || c == '\n')
            .to_owned();

        Ok(SmtpCredentials::new(self.smtp_login.to_owned(), passwd))
    }

    pub fn smtp_starttls(&self) -> bool {
        match self.smtp_starttls {
            Some(true) => true,
            _ => false,
        }
    }

    pub fn smtp_insecure(&self) -> bool {
        match self.smtp_insecure {
            Some(true) => true,
            _ => false,
        }
    }
}

/// # Config
/// This struct holds the global settings of himalaya. Take a look into its
/// [wiki
/// page](https://github.com/soywod/himalaya/wiki/Configuration:config-file#global-settings)
/// for more information.
=======
impl Default for Account {
    fn default() -> Self {
        Self {
            name: None,
            downloads_dir: None,
            signature: None,
            default_page_size: None,
            default: None,
            email: String::new(),
            watch_cmds: None,
            imap_host: String::new(),
            imap_port: 0,
            imap_starttls: None,
            imap_insecure: None,
            imap_login: String::new(),
            imap_passwd_cmd: String::new(),
            smtp_host: String::new(),
            smtp_port: 0,
            smtp_starttls: None,
            smtp_insecure: None,
            smtp_login: String::new(),
            smtp_passwd_cmd: String::new(),
        }
    }
}

// Config

>>>>>>> 27638be387940f6f3fbf1542b96d2131967af944
#[derive(Debug, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub struct Config {
    pub name: String,
    pub downloads_dir: Option<PathBuf>,
    pub notify_cmd: Option<String>,
    pub signature: Option<String>,
    pub default_page_size: Option<usize>,
    pub watch_cmds: Option<Vec<String>>,
    pub tui: TuiConfig,

    #[serde(flatten)]
    pub accounts: HashMap<String, Account>,
}

impl Config {
    /// This function will check if the config file is under
    /// `$XDG_CONFIG_HOME/himalya/config.toml`.
    fn path_from_xdg() -> Result<PathBuf> {
        let path =
            env::var("XDG_CONFIG_HOME").chain_err(|| "Cannot find `XDG_CONFIG_HOME` env var")?;
        let mut path = PathBuf::from(path);
        path.push("himalaya");
        path.push("config.toml");

        Ok(path)
    }

    /// This function will check if the config file is under
    /// `$HOME/.config/himalaya/config.toml`.
    fn path_from_xdg_alt() -> Result<PathBuf> {
        let home_var = if cfg!(target_family = "windows") {
            "USERPROFILE"
        } else {
            "HOME"
        };
        let mut path: PathBuf = env::var(home_var)
            .chain_err(|| format!("Cannot find `{}` env var", home_var))?
            .into();
        path.push(".config");
        path.push("himalaya");
        path.push("config.toml");

        Ok(path)
    }

    /// This function will check the config file at
    /// `$HOME/.himalayarc`.
    fn path_from_home() -> Result<PathBuf> {
        let home_var = if cfg!(target_family = "windows") {
            "USERPROFILE"
        } else {
            "HOME"
        };
        let mut path: PathBuf = env::var(home_var)
            .chain_err(|| format!("Cannot find `{}` env var", home_var))?
            .into();
        path.push(".himalayarc");

        Ok(path)
    }

    pub fn new(path: Option<PathBuf>) -> Result<Self> {
        let path = match path {
            Some(path) => path,
            None => Self::path_from_xdg()
                .or_else(|_| Self::path_from_xdg_alt())
                .or_else(|_| Self::path_from_home())
                .chain_err(|| "Cannot find config path")?,
        };

        let mut file = File::open(path).chain_err(|| "Cannot open config file")?;
        let mut content = vec![];
        file.read_to_end(&mut content)
            .chain_err(|| "Cannot read config file")?;

        Ok(toml::from_slice(&content).chain_err(|| "Cannot parse config file")?)
    }

    /// As the function names says: It returns an an account if it could find
    /// one.
    /// Hint: Accountname is the name between the "[" and "]" brackets of the
    /// config file.
    pub fn find_account_by_name(&self, name: Option<&str>) -> Result<&Account> {
        match name {
            Some(name) => self
                .accounts
                .get(name)
                .ok_or_else(|| format!("Cannot find account `{}`", name).into()),
            None => self
                .accounts
                .iter()
                .find(|(_, account)| account.default.unwrap_or(false))
                .map(|(_, account)| account)
                .ok_or_else(|| "Cannot find default account".into()),
        }
    }

    pub fn downloads_filepath(&self, account: &Account, filename: &str) -> PathBuf {
        account
            .downloads_dir
            .as_ref()
            .unwrap_or(self.downloads_dir.as_ref().unwrap_or(&env::temp_dir()))
            .to_owned()
            .join(filename)
    }

    /// Returns the email address of the provided account.
    pub fn address(&self, account: &Account) -> String {
        let name = account.name.as_ref().unwrap_or(&self.name);
        format!("{} <{}>", name, account.email)
    }

    /// Creates a notification with the given subject from the given sender.
    pub fn run_notify_cmd(&self, subject: &str, sender: &str) -> Result<()> {
        let default_cmd = format!(r#"notify-send "📫 {}" "{}""#, sender, subject);
        let cmd = self
            .notify_cmd
            .as_ref()
            .map(|cmd| format!(r#"{} {:?} {:?}"#, cmd, subject, sender))
            .unwrap_or(default_cmd);

        run_cmd(&cmd).chain_err(|| "Cannot run notify cmd")?;

        Ok(())
    }

    pub fn signature(&self, account: &Account) -> Option<String> {
        let sig = account
            .signature
            .as_ref()
            .or_else(|| self.signature.as_ref());

        sig.and_then(|sig| fs::read_to_string(sig).ok())
            .or_else(|| sig.map(|sig| sig.to_owned()))
    }

    pub fn default_page_size(&self, account: &Account) -> usize {
        account
            .default_page_size
            .as_ref()
            .or_else(|| self.default_page_size.as_ref())
            .or(Some(&DEFAULT_PAGE_SIZE))
            .unwrap()
            .to_owned()
    }

    pub fn exec_watch_cmds(&self, account: &Account) -> Result<()> {
        let cmds = account
            .watch_cmds
            .as_ref()
            .or_else(|| self.watch_cmds.as_ref())
            .map(|cmds| cmds.to_owned())
            .unwrap_or_default();

        thread::spawn(move || {
            debug!("batch execution of {} cmd(s)", cmds.len());
            cmds.iter().for_each(|cmd| {
                debug!("running command {:?}…", cmd);
                let res = run_cmd(cmd);
                debug!("{:?}", res);
            })
        });

        Ok(())
    }
}

impl Default for Config {
    fn default() -> Self {
        Self {
            name: String::new(),
            downloads_dir: None,
            notify_cmd: None,
            signature: None,
            default_page_size: None,
            watch_cmds: None,
            accounts: HashMap::new(),
        }
    }
}
