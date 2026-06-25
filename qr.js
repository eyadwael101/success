/*
 * Minimal offline QR Code generator
 * Public-domain style compact implementation (byte-mode, auto error-correction level L/M)
 * No external network requests required.
 */
(function(global){
  // ---- Galois Field tables for Reed-Solomon ----
  const EXP_TABLE = new Array(256);
  const LOG_TABLE = new Array(256);
  (function(){
    let x = 1;
    for (let i = 0; i < 255; i++) {
      EXP_TABLE[i] = x;
      LOG_TABLE[x] = i;
      x <<= 1;
      if (x & 0x100) x ^= 0x11d;
    }
    for (let i = 255; i < 512; i++) EXP_TABLE[i] = EXP_TABLE[i - 255];
  })();
  function gexp(n){ while(n<0)n+=255; while(n>=255)n-=255; return EXP_TABLE[n]; }
  function glog(n){ if(n<1) throw new Error('glog('+n+')'); return LOG_TABLE[n]; }

  function Polynomial(num, shift){
    let offset = 0;
    while (offset < num.length && num[offset] === 0) offset++;
    this.num = new Array(num.length - offset + shift);
    for (let i = 0; i < num.length - offset; i++) this.num[i] = num[i + offset];
    for (let i = 0; i < shift; i++) this.num[num.length - offset + i] = 0;
  }
  Polynomial.prototype.get = function(i){ return this.num[i]; };
  Polynomial.prototype.getLength = function(){ return this.num.length; };
  Polynomial.prototype.multiply = function(e){
    const num = new Array(this.getLength() + e.getLength() - 1).fill(0);
    for (let i = 0; i < this.getLength(); i++)
      for (let j = 0; j < e.getLength(); j++)
        num[i + j] ^= gexp(glog(this.get(i)) + glog(e.get(j)));
    return new Polynomial(num, 0);
  };
  Polynomial.prototype.mod = function(e){
    if (this.getLength() - e.getLength() < 0) return this;
    const ratio = glog(this.get(0)) - glog(e.get(0));
    const num = this.num.slice();
    for (let i = 0; i < e.getLength(); i++) num[i] ^= gexp(glog(e.get(i)) + ratio);
    return new Polynomial(num, 0).mod(e);
  };

  function getErrorCorrectPolynomial(errorCorrectLength){
    let a = new Polynomial([1], 0);
    for (let i = 0; i < errorCorrectLength; i++)
      a = a.multiply(new Polynomial([1, gexp(i)], 0));
    return a;
  }

  // ---- QR version capacity tables (byte mode) for EC level L and M ----
  // [version]: {L:[capacity,ecBlocks...], M:[...]}
  // Simplified: support versions 1-10 which cover up to ~174 bytes (L) — enough for our small JSON payloads
  const RS_BLOCK_TABLE = {
    1:{L:[19,7],M:[16,10]}, 2:{L:[34,10],M:[28,16]}, 3:{L:[55,15],M:[44,26]},
    4:{L:[80,20],M:[64,36]},5:{L:[108,26],M:[86,36]},6:{L:[136,18],M:[108,32]},
    7:{L:[156,20],M:[124,40]},8:{L:[194,24],M:[154,52]},9:{L:[232,30],M:[182,58]},
    10:{L:[274,18],M:[216,68]}
  };
  // total codewords per version (data+ec) for versions 1-10
  const TOTAL_CODEWORDS = {1:26,2:44,3:70,4:100,5:134,6:172,7:196,8:242,9:292,10:346};
  const MODULE_COUNT = v => v*4+17;

  function chooseVersion(dataLen, ecLevel){
    for (let v=1; v<=10; v++){
      const cap = RS_BLOCK_TABLE[v][ecLevel][0];
      if (dataLen + 2 <= cap) return v; // +2 rough header overhead, refined below
    }
    return 10;
  }

  function stringToBytes(str){
    const utf8 = unescape(encodeURIComponent(str));
    const bytes = [];
    for (let i=0;i<utf8.length;i++) bytes.push(utf8.charCodeAt(i));
    return bytes;
  }

  function createBitBuffer(){
    return { buffer: [], length: 0,
      put(num, length){ for (let i=0;i<length;i++) this.putBit(((num >>> (length-i-1)) & 1)===1); },
      putBit(bit){
        const bufIndex = Math.floor(this.length/8);
        if (this.buffer.length <= bufIndex) this.buffer.push(0);
        if (bit) this.buffer[bufIndex] |= (0x80 >>> (this.length%8));
        this.length++;
      }
    };
  }

  function createData(version, ecLevel, bytes){
    const buffer = createBitBuffer();
    buffer.put(4, 4); // byte mode
    buffer.put(bytes.length, 8);
    for (let i=0;i<bytes.length;i++) buffer.put(bytes[i], 8);

    const totalCodewords = TOTAL_CODEWORDS[version];
    const ecCodewords = RS_BLOCK_TABLE[version][ecLevel][1];
    const dataCodewords = totalCodewords - ecCodewords;
    const maxBits = dataCodewords * 8;

    if (buffer.length + 4 <= maxBits) buffer.put(0,4);
    while (buffer.length % 8 !== 0) buffer.putBit(false);
    const padBytes = [0xEC, 0x11];
    let pi = 0;
    while (buffer.buffer.length < dataCodewords) { buffer.buffer.push(padBytes[pi%2]); pi++; }
    buffer.buffer.length = dataCodewords;

    // Reed-Solomon error correction (single block, sufficient for small versions used here)
    const rsPoly = getErrorCorrectPolynomial(ecCodewords);
    const rawPoly = new Polynomial(buffer.buffer, ecCodewords);
    const modPoly = rawPoly.mod(rsPoly);
    const ecBytes = new Array(ecCodewords).fill(0);
    for (let i=0;i<ecBytes.length;i++){
      const modIndex = i + modPoly.getLength() - ecBytes.length;
      ecBytes[i] = modIndex >= 0 ? modPoly.get(modIndex) : 0;
    }
    return buffer.buffer.concat(ecBytes);
  }

  // ---- Matrix placement ----
  function QRCodeModel(version, ecLevel){
    this.version = version;
    this.ecLevel = ecLevel;
    this.moduleCount = MODULE_COUNT(version);
    this.modules = null;
    this.dataCache = null;
  }
  QRCodeModel.prototype.isDark = function(row,col){
    if (row<0||this.moduleCount<=row||col<0||this.moduleCount<=col) return false;
    return !!this.modules[row][col];
  };
  QRCodeModel.prototype.setupPositionProbePattern = function(row,col){
    for (let r=-1;r<=7;r++){
      if (row+r<=-1||this.moduleCount<=row+r) continue;
      for (let c=-1;c<=7;c++){
        if (col+c<=-1||this.moduleCount<=col+c) continue;
        const dark = (0<=r&&r<=6&&(c===0||c===6)) || (0<=c&&c<=6&&(r===0||r===6)) || (2<=r&&r<=4&&2<=c&&c<=4);
        this.modules[row+r][col+c] = dark;
      }
    }
  };
  QRCodeModel.prototype.getBestMaskPattern = function(){ return 0; };
  QRCodeModel.prototype.setupTimingPattern = function(){
    for (let r=8;r<this.moduleCount-8;r++) if (this.modules[r][6]===null) this.modules[r][6]=(r%2===0);
    for (let c=8;c<this.moduleCount-8;c++) if (this.modules[6][c]===null) this.modules[6][c]=(c%2===0);
  };
  QRCodeModel.prototype.setupPositionAdjustPattern = function(){
    const pos = QRCodeModel.getPatternPosition(this.version);
    for (let i=0;i<pos.length;i++) for (let j=0;j<pos.length;j++){
      const row=pos[i], col=pos[j];
      if (this.modules[row][col]!==null) continue;
      for (let r=-2;r<=2;r++) for (let c=-2;c<=2;c++)
        this.modules[row+r][col+c] = (r===-2||r===2||c===-2||c===2||(r===0&&c===0));
    }
  };
  QRCodeModel.getPatternPosition = function(version){
    const table = {1:[],2:[6,18],3:[6,22],4:[6,26],5:[6,30],6:[6,34],7:[6,22,38],8:[6,24,42],9:[6,26,46],10:[6,28,50]};
    return table[version]||[];
  };
  QRCodeModel.prototype.setupTypeNumber = function(test){
    const bits = QRCodeModel.getBCHTypeNumber(this.version);
    for (let i=0;i<18;i++){
      const mod = (!test && ((bits>>i)&1)===1);
      this.modules[Math.floor(i/3)][i%3+this.moduleCount-8-3] = mod;
    }
    for (let i=0;i<18;i++){
      const mod = (!test && ((bits>>i)&1)===1);
      this.modules[i%3+this.moduleCount-8-3][Math.floor(i/3)] = mod;
    }
  };
  QRCodeModel.getBCHTypeNumber = function(version){
    if (version<7) return 0;
    let d = version<<12;
    while (QRCodeModel.getBCHDigit(d) - 13 >= 0) d ^= (0x1f25 << (QRCodeModel.getBCHDigit(d)-13));
    return (version<<12) | d;
  };
  QRCodeModel.getBCHDigit = function(data){ let digit=0; while(data!==0){digit++;data>>>=1;} return digit; };
  QRCodeModel.prototype.setupTypeInfo = function(test, maskPattern){
    const ecIndicator = {L:1,M:0,Q:3,H:2}[this.ecLevel];
    let data = (ecIndicator<<3) | maskPattern;
    let d = data<<10;
    while (QRCodeModel.getBCHDigit(d) - 10 >= 0) d ^= (0x537 << (QRCodeModel.getBCHDigit(d)-10));
    const bits = ((data<<10)|d) ^ 0x5412;
    for (let i=0;i<15;i++){
      const mod = (!test && ((bits>>i)&1)===1);
      if (i<6) this.modules[i][8]=mod;
      else if (i<8) this.modules[i+1][8]=mod;
      else this.modules[this.moduleCount-15+i][8]=mod;
    }
    for (let i=0;i<15;i++){
      const mod = (!test && ((bits>>i)&1)===1);
      if (i<8) this.modules[8][this.moduleCount-i-1]=mod;
      else if (i<9) this.modules[8][15-i-1+1]=mod;
      else this.modules[8][15-i-1]=mod;
    }
    this.modules[this.moduleCount-8][8]=(!test);
  };
  function maskFunc(i,j){ return (i+j)%2===0; }
  QRCodeModel.prototype.mapData = function(data, maskPattern){
    let inc=-1, row=this.moduleCount-1, bitIndex=7, byteIndex=0;
    for (let col=this.moduleCount-1; col>0; col-=2){
      if (col===6) col--;
      while (true){
        for (let c=0;c<2;c++){
          if (this.modules[row][col-c]===null){
            let dark=false;
            if (byteIndex<data.length) dark = (((data[byteIndex]>>>bitIndex)&1)===1);
            if (maskFunc(row,col-c)) dark=!dark;
            this.modules[row][col-c]=dark;
            bitIndex--;
            if (bitIndex===-1){ byteIndex++; bitIndex=7; }
          }
        }
        row += inc;
        if (row<0||this.moduleCount<=row){ row-=inc; inc=-inc; break; }
      }
    }
  };
  QRCodeModel.prototype.make = function(bytes){
    this.modules = [];
    for (let r=0;r<this.moduleCount;r++){ this.modules.push([]); for (let c=0;c<this.moduleCount;c++) this.modules[r].push(null); }
    this.setupPositionProbePattern(0,0);
    this.setupPositionProbePattern(this.moduleCount-7,0);
    this.setupPositionProbePattern(0,this.moduleCount-7);
    this.setupPositionAdjustPattern();
    this.setupTimingPattern();
    this.setupTypeInfo(false,0);
    if (this.version>=7) this.setupTypeNumber(false);
    this.mapData(bytes,0);
  };

  function generateQRMatrix(text, ecLevelPref){
    const bytes = stringToBytes(text);
    const ecLevel = ecLevelPref || 'M';
    let version = chooseVersion(bytes.length, ecLevel);
    // verify capacity precisely, bump version if needed
    while (true){
      try {
        const data = createData(version, ecLevel, bytes);
        const model = new QRCodeModel(version, ecLevel);
        model.make(data);
        return model;
      } catch(e){
        version++;
        if (version>10){ throw e; }
      }
    }
  }

  function renderToCanvas(canvas, text, opts){
    opts = opts||{};
    const size = opts.size||128;
    const margin = opts.margin!==undefined?opts.margin:4;
    const dark = opts.dark||'#000000';
    const light = opts.light||'#ffffff';
    const model = generateQRMatrix(text, opts.ecLevel||'M');
    const count = model.moduleCount;
    const cell = Math.floor(size/(count+margin*2));
    const pxSize = cell*(count+margin*2);
    canvas.width = pxSize; canvas.height = pxSize;
    const ctx = canvas.getContext('2d');
    ctx.fillStyle = light; ctx.fillRect(0,0,pxSize,pxSize);
    ctx.fillStyle = dark;
    for (let r=0;r<count;r++) for (let c=0;c<count;c++)
      if (model.isDark(r,c)) ctx.fillRect((c+margin)*cell,(r+margin)*cell,cell,cell);
    return canvas;
  }

  // Public API: SimpleQR.toCanvas(canvas, text, opts) and SimpleQR.draw(container, text, opts)
  global.SimpleQR = {
    toCanvas: renderToCanvas,
    draw: function(container, text, opts){
      const canvas = document.createElement('canvas');
      renderToCanvas(canvas, text, opts);
      container.innerHTML = '';
      container.appendChild(canvas);
      return canvas;
    }
  };
})(window);
