// import the Anchor library
import * as anchor from '@project-serum/anchor';
// Read the generated IDL
import idl from '../../../target/idl/solblog.json';

// we can do this because svektekit/vite allows us to import json file as es modules :)
import solConfigFile from '../../../deploy/solana-config.json';
import keyfile from '../../../deploy/programauthority-keypair.json';
import solblog_keypair from '../../../target/deploy/solblog-keypair.json';

import { WalletAdaptorPhantom } from '$lib/helpers/wallet-adapter-phantom';

const { SystemProgram } = anchor.web3; // Added to initialize account

let utf8decoder = new TextDecoder(); // default 'utf-8' or 'utf8'

const opts = {
	preflightCommitment: 'recent',
	commitment: 'recent'
};

const getDevPgmId = () => {
	// get the program ID from the solblog-keyfile.json
	let pgmKeypair = anchor.web3.Keypair.fromSecretKey(new Uint8Array(solblog_keypair));
	return new anchor.web3.PublicKey(pgmKeypair.publicKey); // Address of the deployed program
};

export default class AnchorClient {
	// you can make an anchor program without a provider
	// then set the provider later with anchor.setProvider
	// you just won't be able to init or makePost until a wallet provider is set up
	constructor({ programId, config, keypair } = {}) {
		this.programId = programId || getDevPgmId();
		this.config = config || solConfigFile.development.config;
		this.connection = new anchor.web3.Connection(this.config.httpUri, 'confirmed');
		console.log('\n\nConnected to', this.config.httpUri);

		const wallet =
			window.solana.isConnected && window.solana?.isPhantom
				? new WalletAdaptorPhantom()
				: keypair
				? new anchor.Wallet(keypair)
				: new anchor.Wallet(anchor.web3.Keypair.generate());
		// maps anchor calls to Phantom direction
		this.provider = new anchor.Provider(this.connection, wallet, opts);
		this.program = new anchor.Program(idl, programId, this.provider);
	}

	setWallet(keypair = false) {
		const wallet =
			window.solana.isConnected && window.solana?.isPhantom
				? new WalletAdaptorPhantom()
				: keypair
				? new anchor.Wallet(keypair)
				: new anchor.Wallet(anchor.web3.Keypair.generate());
		this.provider = new anchor.Provider(this.connection, wallet, opts);
		anchor.setProvider(this.provider);
	}

	async initialize() {
		let blogAccount = anchor.web3.Keypair.generate();

		// Execute the RPC.
		const tx = await this.program.rpc.initialize(
			// provider.wallet.payer.publicKey,
			{
				accounts: {
					blogAccount: blogAccount.publicKey, // we're re-using our wallet keys for simplicity, but you can pass in any keypair you like
					authority: this.provider.wallet.publicKey, // just for Anchor reference
					systemProgram: SystemProgram.programId // just for Anchor reference
				},
				signers: [blogAccount] // , provider.wallet.payer
			}
		);
		console.log(
			`Successfully intialized Blog ID: ${blogAccount.publicKey} for Blogger ${this.provider.wallet.publicKey}`
		);
		return blogAccount;
	}

	async makePost(post, blogAccountStr) {
		// convert out text string to UTF8 bytes
		// const encoder = new TextEncoder();
		let utf8decoder = new TextDecoder(); // default 'utf-8' or 'utf8'
		let provider = this.program.provider;
		let blogAccount = new anchor.web3.PublicKey(blogAccountStr);

		const utf8encoded = Buffer.from(post); // encoder.encode(post); // doesn't like UInt8Array?
		console.log('blogAccount: ', { blogAccount }, blogAccount.publicKey, {
			provider: this.program
		});
		// Execute the RPC.
		const tx = await this.program.rpc.makePost(
			// input must be compatible with UTF8 Vector in rust
			utf8encoded,
			// now pass the accounts in
			{
				accounts: {
					blogAccount: blogAccount, // we're re-using our wallet keys for simplicity, but you can pass in any keypair you like
					authority: this.program.provider.wallet.publicKey // just for Anchor reference
				},
				signers: [this.program.provider.wallet.payer]
			}
		);
		console.log(
			`Successfully posted ${post} to https://explorer.solana.com/address/${blogAccount}?cluster=devnet`
		);
		return tx;
	}

	// never really used, but a good example of how to use Anchor to read an account
	async getLatestPost(blogAccount) {
		const account = await this.program.account.blogAccount.fetch(blogAccount.publicKey);
		console.log(`get account latest post:`, { account });
		return utf8decoder.decode(account.latestPost);
	}

	getBlogAuthority = async (blogid) => {
		let accountInfo = await this.program.account.blogAccount.fetch(
			new anchor.web3.PublicKey(blogid)
		);
		// You could do this, but you've got to parse the buffer data (tpyed array) yourself.... ew.
		// let accountInfo = await connection.getAccountInfo(new anchor.web3.PublicKey(blogid));
		console.log({ accountInfo });
		return accountInfo.authority.toString();
	};
	// dev only, use dev connection
	airDrop = async (publicKey, lamports = 500000000) => {
		// CLI: solana airdrop --url devnet 1 <recipientaddress>
		const signature = await this.connection.requestAirdrop(
			new anchor.web3.PublicKey(publicKey),
			lamports
		);
		await this.connection.confirmTransaction(signature);
		return await this.getBalance(publicKey);
	};

	getBalance = async (publicKey) => {
		return await this.connection.getBalance(new anchor.web3.PublicKey(publicKey));
	};

	// Read is a pure Solana Web3.js exercise, no Anchor really needed
	getLastPosts = async (blogid, limit = 100) => {
		console.log({ blogid }, { limit });
		const accountpublicKey = new anchor.web3.PublicKey(blogid);

		const parsedConfirmedTransactions = await this.getTransactionForAddress(accountpublicKey);

		const filtered = parsedConfirmedTransactions.filter((tx) =>
			tx.meta.logMessages.some((msg) => msg.startsWith('Program log:'))
		);

		const postDetails = filtered.map((tx) => {
			const timestamp = new Date(tx.blockTime * 1000).toString();
			const pgmLogs = tx.meta.logMessages.filter((msg) => msg.startsWith('Program log: '));
			const content = pgmLogs.map((log) => log.substring('Program log: '.length));
			return { content, timestamp, signature: tx.transaction.signatures[0] };
		});

		return postDetails;
	};

	getTransactionForAddress = async (publicKey, limit = 100) => {
		const confirmedSignatureInfo = await this.connection.getSignaturesForAddress(
			new anchor.web3.PublicKey(publicKey),
			{ limit }
		);

		const transactionSignatures = confirmedSignatureInfo.map((sigInfo) => sigInfo.signature);
		const parsedConfirmedTransactions = await this.connection.getParsedConfirmedTransactions(
			transactionSignatures
		);
		return parsedConfirmedTransactions;
	};
	getBlogAccounts = async (publicKey) => {
		// 1) Find all Tx for this PublicKey
		// 2) Filter to Tx that have programId == our ProgramId
		// 3) Get addresses (pubkeys) for that Tx, separate them into A) Payer, Program, and BlogAccount
		// 4) List the different accounts
		const parsedConfirmedTransactions = await this.getTransactionForAddress(publicKey);

		let blogAccounts = [];

		// filter these tx where there are some programIds as pubkey
		parsedConfirmedTransactions.forEach((tx) => {
			// look for Create Account instructions and find the "new Address" from the blogger ID address
			let instr = tx?.meta?.innerInstructions[0]?.instructions[0]?.parsed;
			if (
				!instr ||
				!(instr.type === 'createAccount' && instr.info.owner == this.programId.toString())
			)
				return;
			console.log({ tx });
			blogAccounts.push(tx.meta.innerInstructions[0].instructions[0].parsed.info.newAccount);
			console.log({ blogAccounts }, 1);

			return;

			tx.transaction.message.accountKeys.forEach((key, index, orig) => {
				// exclude keys that dont include this programId
				if (key.pubkey.toString() !== this.programId.toString()) return;
				console.log({ tx });

				let account = tx.transaction.message.accountKeys.find((key) => {
					// writable && signer == payer (already known)
					// !writable && !signer == program (already known)
					// writable && !signer == blogAccount
					console.log({ key });
					return key.writable && key.signer;
				});
				if (!account) {
					// happens when Account is originally created, so we can discard this match
					// it happens because at creation, blogAccount is a signer too (key.signer=true)
					console.log(
						`https://explorer.solana.com/address/${tx.transaction.signatures[0]}?cluster=devnet`
					);
					return;
				}
				if (!blogAccounts.includes(account.pubkey.toString()))
					blogAccounts.push(account.pubkey.toString());
			});
		});
		console.log({ blogAccounts }, 2);

		return blogAccounts;
	};
}
