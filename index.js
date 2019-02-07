const { lp, string_read_text } = require('./tml');

function load_stream(stream) { // loads stream into string
	return new Promise((resolve, reject) => {
		let data = '';
		stream.on('readable', () => {
      while ((chunk = stream.read()) !== null)
        data += chunk;
		});
		stream.on('end', () => resolve(data));
		stream.on('error', reject);    
	});
}

async function main() {
	let s;
	try {
		process.stdin.setEncoding('utf8');
    s = string_read_text(await load_stream(process.stdin));  
	} catch (err) {
		console.log(err); // stdin read error
	}
	const p = new lp();
	p.prog_read(s);
	if (!p.pfp()) console.log('unsat');
}

main();
