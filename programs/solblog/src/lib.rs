use anchor_lang::prelude::*;
use std::str::from_utf8;
//use anchor_lang::prelude::*;
use anchor_lang::Discriminator;
use solana_program::entrypoint::ProgramResult;
use arrayref::array_ref;
use gem_common::{errors::ErrorCode, *};
use metaplex_token_metadata::state::Metadata;
use anchor_spl::token::{Mint, TokenAccount};
use std::str::FromStr;

declare_id!("3UctCe6uCKMvngtt993jM4jnXHs4hsQnLmgguWVRDwNx");

#[program]
pub mod solblog {
    use super::*;
    pub fn initialize(
        ctx: Context<Initialize>, // <-- Anchor context that holds all the account data (structs) below
        new_bio: Vec<u8>,         // <--- our blog post bio
    ) -> ProgramResult {
        // <--- These functions are snake_case of the CamelCase struct below
        let b_p_a = &mut ctx.accounts.blog_account; // grab a mutable reference to our BlogAccount struct
        b_p_a.authority = *ctx.accounts.authority.key; // set the BlogAccount.authority to the pubkey of the authority
        b_p_a.bio = new_bio.to_vec(); // save the latest bio in the account.
        let bio = from_utf8(&new_bio) // convert the array of bytes into a string slice
            .map_err(|err| {
                msg!("Invalid UTF-8, from byte {}", err.valid_up_to());
                ProgramError::InvalidInstructionData
            })?;
        msg!(bio);
        Ok(()) // return the Result
    }

    pub fn make_post(
        ctx: Context<MutateAccount>,
        new_post: Vec<u8>, // <--- our blog post data
    ) -> ProgramResult {
        assert_whitelisted(&ctx)?;
        let post = from_utf8(&new_post) // convert the array of bytes into a string slice
            .map_err(|err| {
                msg!("Invalid UTF-8, from byte {}", err.valid_up_to());
                ProgramError::InvalidInstructionData
            })?;
        msg!(post); // msg!() is a Solana macro that prints string slices to the program log, which we can grab from the transaction block data

        let b_acc = &mut ctx.accounts.blog_account;
        b_acc.latest_post = new_post; // save the latest post in the account.
                                      // past posts will be saved in transaction logs

        Ok(()) // return ok result
    }
    pub fn update_bio(
        ctx: Context<MutateAccount>,
        new_bio: Vec<u8>, // <--- our blog post bio
    ) -> ProgramResult {
        let b_acc = &mut ctx.accounts.blog_account;
        b_acc.bio = new_bio; // save the latest bio in the account.
        Ok(()) // return ok result
    }
    pub fn add_to_whitelist(ctx: Context<AddToWhitelist>, whitelist_type: u8) -> Result<()> {
        {
            let acct = ctx.accounts.whitelist_proof.to_account_info();
            let data: &[u8] = &acct.try_borrow_data()?;
            let disc_bytes = array_ref![data, 0, 8];
            if disc_bytes != &WhitelistProof::discriminator() && disc_bytes.iter().any(|a| a != &0) {
                return Err(error!(ErrorCode::AccountDiscriminatorMismatch));
            }
        }
    
        // create/update whitelist proof
        let proof = &mut ctx.accounts.whitelist_proof;
    
        // if this is an update, decrement counts from existing whitelist
        if proof.whitelist_type > 0 {
            let existing_whitelist = WhitelistProof::read_type(proof.whitelist_type)?;
            let blog = &mut ctx.accounts.blog;
    
            if existing_whitelist.contains(WhitelistType::CREATOR) {
                blog.whitelisted_creators.try_sub_assign(1)?;
            }
            if existing_whitelist.contains(WhitelistType::MINT) {
                blog.whitelisted_mints.try_sub_assign(1)?;
            }
        }
    
        // record new whitelist and increment counts
        let new_whitelist = WhitelistProof::read_type(whitelist_type)?;
    
        proof.reset_type(new_whitelist);
        proof.whitelisted_address = ctx.accounts.address_to_whitelist.key();
        proof.blog = ctx.accounts.blog.key();
    
        let blog = &mut ctx.accounts.blog;
    
        if new_whitelist.contains(WhitelistType::CREATOR) {
            blog.whitelisted_creators.try_add_assign(1)?;
        }
        if new_whitelist.contains(WhitelistType::MINT) {
            blog.whitelisted_mints.try_add_assign(1)?;
        }
    
        // msg!(
        //     "{} added to whitelist",
        //     &ctx.accounts.address_to_whitelist.key()
        // );
        Ok(())
    }
}

#[derive(Accounts)]
pub struct Initialize<'info> {
    #[account(
        init, // hey Anchor, initialize an account with these details for me
        payer = authority, // See that authority Signer (pubkey) down there? They're paying for this 
        space = 8 // all accounts need 8 bytes for the account discriminator prepended to the account
        + 32 // authority: Pubkey needs 32 bytes
        + 566 // latest_post: post bytes could need up to 566 bytes for the memo
        + 256 // bytes of meta data (name, about, link.in.bio, etc)
        // You have to do this math yourself, there's no macro for this
    )]
    pub blog_account: Account<'info, BlogAccount>, // <--- initialize this account variable & add it to Context and can be used above ^^ in our initialize function
    #[account(mut)]
    pub authority: Signer<'info>, // <--- let's name the account that signs this transaction "authority" and make it mutable so we can set the value to it in `initialize` function above
    pub system_program: Program<'info, System>, // <--- Anchor boilerplate
}

#[derive(Accounts)]
pub struct MutateAccount<'info> {
    /*#[account(
        mut, // we can make changes to this account
        has_one = authority
    )] // the authority has signed this post, allowing it to happen */

    // this is here again because it holds that .latest_post field where our post is saved
    #[account(mut)]
    pub blog_account: Box<Account<'info, BlogAccount>>, // <-- enable this account to also be used in the make_post function
    pub nft_source: Box<Account<'info, TokenAccount>>,
    pub nft_mint: Box<Account<'info, Mint>>,
    pub authority: Signer<'info>,
}

#[account]
pub struct BlogAccount {
    pub latest_post: Vec<u8>, // <-- where the latest blog post will be stored
    pub bio: Vec<u8>,
    pub whitelisted_mints: u32,
    pub whitelisted_creators: u32,
    pub authority: Pubkey,
}


#[derive(Accounts)]
pub struct AddToWhitelist<'info> {
    #[account(mut, has_one = authority)]
    pub blog: Box<Account<'info, BlogAccount>>,
    pub authority: Signer<'info>,

    // whitelist
    /// CHECK:
    pub address_to_whitelist: AccountInfo<'info>,
    // must stay init_as_needed, otherwise no way to change afterwards
    #[account(init_if_needed,
        seeds = [
            b"whitelist".as_ref(),
            blog.key().as_ref(),
            address_to_whitelist.key().as_ref(),
        ],
        bump,
        payer = payer,
        space = 8 + std::mem::size_of::<WhitelistProof>())]
    pub whitelist_proof: Box<Account<'info, WhitelistProof>>,

    // misc
    #[account(mut)]
    pub payer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[account]
pub struct WhitelistProof {
    pub whitelist_type: u8,

    pub whitelisted_address: Pubkey,

    pub blog: Pubkey,
    //no reserved space coz super scarce space already
}

impl WhitelistProof {
    pub fn read_type(whitelist_type: u8) -> Result<WhitelistType> {
        WhitelistType::from_bits(whitelist_type).ok_or(error!(ErrorCode::InvalidParameter))
    }

    pub fn reset_type(&mut self, whitelist_type: WhitelistType) {
        self.whitelist_type = whitelist_type.bits();
    }

    pub fn contains_type(&self, expected_whitelist_type: WhitelistType) -> Result<()> {
        let whitelist_type = WhitelistProof::read_type(self.whitelist_type)?;
        if whitelist_type.contains(expected_whitelist_type) {
            // msg!(
            //     "whitelist type ({:?}) matches, going ahead",
            //     expected_whitelist_type
            // );
            return Ok(());
        }

        Err(error!(ErrorCode::WrongWhitelistType))
    }
} 
bitflags::bitflags! {
    pub struct WhitelistType: u8 {
        const CREATOR = 1 << 0;
        const MINT = 1 << 1;
    }
} 

#[event]
pub struct PostEvent {
    pub label: String,
    pub post_id: Pubkey,
    pub next_post_id: Option<Pubkey>,
}
// helper functions for checking that the user has a doug/monk
fn assert_valid_metadata(
    gem_metadata: &AccountInfo,
    gem_mint: &Pubkey,
) -> core::result::Result<Metadata, ProgramError> {
    let metadata_program = Pubkey::from_str("metaqbxxUerdq28cj1RbAWkYQm3ybzjb6a8bt518x1s").unwrap();

    // 1 verify the owner of the account is metaplex's metadata program
    assert_eq!(gem_metadata.owner, &metadata_program);

    // 2 verify the PDA seeds match
    let seed = &[
        b"metadata".as_ref(),
        metadata_program.as_ref(),
        gem_mint.as_ref(),
    ];

    let (metadata_addr, _bump) = Pubkey::find_program_address(seed, &metadata_program);
    assert_eq!(metadata_addr, gem_metadata.key());

    Metadata::from_account_info(gem_metadata)
}

fn assert_valid_whitelist_proof<'info>(
    whitelist_proof: &AccountInfo<'info>,
    bank: &Pubkey,
    address_to_whitelist: &Pubkey,
    program_id: &Pubkey,
    expected_whitelist_type: WhitelistType,
) -> Result<()> {
    // 1 verify the PDA seeds match
    let seed = &[
        b"whitelist".as_ref(),
        bank.as_ref(),
        address_to_whitelist.as_ref(),
    ];
    let (whitelist_addr, _bump) = Pubkey::find_program_address(seed, program_id);

    // we can't use an assert_eq statement, we want to catch this error and continue along to creator testing
    if whitelist_addr != whitelist_proof.key() {
        return Err(error!(ErrorCode::NotWhitelisted));
    }

    // 2 no need to verify ownership, deserialization does that for us
    // https://github.com/project-serum/anchor/blob/fcb07eb8c3c9355f3cabc00afa4faa6247ccc960/lang/src/account.rs#L36
    let proof = Account::<'info, WhitelistProof>::try_from(whitelist_proof)?;

    // 3 verify whitelist type matches
    proof.contains_type(expected_whitelist_type)
}

fn assert_whitelisted(ctx: &Context<MutateAccount>) -> Result<()> {
    let bank = &*ctx.accounts.blog_account;
    let mint = &*ctx.accounts.nft_mint;
    let remaining_accs = &mut ctx.remaining_accounts.iter();

    // whitelisted mint is always the 1st optional account
    // this is because it's applicable to both NFTs and standard fungible tokens
    let mint_whitelist_proof_info = next_account_info(remaining_accs)?;

    // attempt to verify based on mint
    if bank.whitelisted_mints > 0 {
        if let Ok(()) = assert_valid_whitelist_proof(
            mint_whitelist_proof_info,
            &bank.key(),
            &mint.key(),
            ctx.program_id,
            WhitelistType::MINT,
        ) {
            // msg!("mint whitelisted: {}, going ahead", &mint.key());
            return Ok(());
        }
    }

    // if mint verification above failed, attempt to verify based on creator
    if bank.whitelisted_creators > 0 {
        // 2 additional accounts are expected - metadata and creator whitelist proof
        let metadata_info = next_account_info(remaining_accs)?;
        let creator_whitelist_proof_info = next_account_info(remaining_accs)?;

        // verify metadata is legit
        let metadata = assert_valid_metadata(metadata_info, &mint.key())?;

        // metaplex constraints this to max 5, so won't go crazy on compute
        // (empirical testing showed there's practically 0 diff between stopping at 0th and 5th creator)
        for creator in &metadata.data.creators.unwrap() {
            // verify creator actually signed off on this nft
            if !creator.verified {
                continue;
            }

            // check if creator is whitelisted, returns an error if not
            let attempted_proof = assert_valid_whitelist_proof(
                creator_whitelist_proof_info,
                &bank.key(),
                &creator.address,
                ctx.program_id,
                WhitelistType::CREATOR,
            );

            match attempted_proof {
                //proof succeeded, return out of the function, no need to continue looping
                Ok(()) => return Ok(()),
                //proof failed, continue to check next creator
                Err(_e) => continue,
            }
        }
    }

    // if both conditions above failed tok return Ok(()), then verification failed
    Err(error!(ErrorCode::NotWhitelisted))
}