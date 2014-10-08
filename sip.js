var util = require('util');
var net = require('net');
var dns = require('dns');
var assert = require('assert');
var dgram = require('dgram');
var tls = require('tls');
var https = require('https');
var fs = require('fs');
var os = require('os');
var crypto = require('crypto');

var myLogger = {
    trace: function() {},
    debug: function() {},
    info: function() {},
    warn: function() {},
    error: function() {},
    fatal: function() {},
};

try {
    var WebSocket = require('ws');
}
catch(e) {
}

function debug(e) {
    if (e && e.stack) {
        util.debug(e + '\n' + e.stack);
    }
    else {
        util.debug(util.inspect(e));
    }
}

function toBase64(s) {
    switch(s.length % 3) {
    case 1:
        s += '  ';
        break;
    case 2:
        s += ' ';
        break;
    default:
    }

    return (new Buffer(s)).toString('base64').replace(/\//g, '_').replace(/\+/g, '-');
}
// Actual stack code begins here

function parseResponse(rs, m) {
    var r = rs.match(/^SIP\/(\d+\.\d+)\s+(\d+)\s*(.*)\s*$/);

    if(r) {
        m.version = r[1];
        m.status = +r[2];
        m.reason = r[3];

        return m;
    }
}

function parseRequest(rq, m) {
    var r = rq.match(/^([\w\-.!%*_+`'~]+)\s([^\s]+)\sSIP\s*\/\s*(\d+\.\d+)/);

    if(r) {
        m.method = unescape(r[1]);
        m.uri = r[2];
        m.version = r[3];

        return m;
    }
}

function applyRegex(regex, data) {
    regex.lastIndex = data.i;
    var r = regex.exec(data.s);

    if(r && (r.index === data.i)) {
        data.i = regex.lastIndex;
        return r;
    }
}

function parseParams(data, hdr) {
    hdr.params = hdr.params || {};

    var re = /\s*;\s*([\w\-.!%*_+`'~]+)(?:\s*=\s*([\w\-.!%*_+`'~]+|"[^"\\]*(\\.[^"\\]*)*"))?/g;

    for(var r = applyRegex(re, data); r; r = applyRegex(re, data)) {
        hdr.params[r[1].toLowerCase()] = r[2];
    }

    return hdr;
}

function parseMultiHeader(parser, d, h) {
    h = h || [];

    var re = /\s*,\s*/g;
    do {
        h.push(parser(d));
    } while(d.i < d.s.length && applyRegex(re, d));

    return h;
}

function parseGenericHeader(d, h) {
    return h ? h + ',' + d.s : d.s;
}

function parseAOR(data) {
    var r = applyRegex(/((?:[\w\-.!%*_+`'~]+)(?:\s+[\w\-.!%*_+`'~]+)*|"[^"\\]*(?:\\.[^"\\]*)*")?\s*<\s*([^>]*)\s*>|((?:[^\s@"<]@)?[^\s;]+)/g, data);

    return parseParams(data, {name: r[1], uri: r[2] || r[3] || ''});
}
exports.parseAOR = parseAOR;

function parseAorWithUri(data) {
    var r = parseAOR(data);
    r.uri = parseUri(r.uri);
    return r;
}

function parseVia(data) {
    var r = applyRegex(/SIP\s*\/\s*(\d+\.\d+)\s*\/\s*([\S]+)\s+([^\s;:]+)(?:\s*:\s*(\d+))?/g, data);
    return parseParams(data, {version: r[1], protocol: r[2], host: r[3], port: r[4] && +r[4]});
}

function parseCSeq(d) {
    var r = /(\d+)\s*([\S]+)/.exec(d.s);
    return { seq: +r[1], method: unescape(r[2]) };
}

function parseAuthHeader(d) {
    var r1 = applyRegex(/([^\s]*)\s+/g, d);
    var a = {scheme: r1[1]};

    var r2 = applyRegex(/([^\s,"=]*)\s*=\s*([^\s,"]+|"[^"\\]*(?:\\.[^"\\]*)*")\s*/g, d);
    a[r2[1]]=r2[2];

    while(r2 = applyRegex(/,\s*([^\s,"=]*)\s*=\s*([^\s,"]+|"[^"\\]*(?:\\.[^"\\]*)*")\s*/g, d)) {
        a[r2[1]]=r2[2];
    }

    return a;
}

function parseAuthenticationInfoHeader(d) {
    var a = {};
    var r = applyRegex(/([^\s,"=]*)\s*=\s*([^\s,"]+|"[^"\\]*(?:\\.[^"\\]*)*")\s*/g, d);
    a[r[1]]=r[2];

    while(r = applyRegex(/,\s*([^\s,"=]*)\s*=\s*([^\s,"]+|"[^"\\]*(?:\\.[^"\\]*)*")\s*/g, d)) {
        a[r[1]]=r[2];
    }
    return a;
}

var compactForm = {
    i: 'call-id',
    m: 'contact',
    e: 'contact-encoding',
    l: 'content-length',
    c: 'content-type',
    f: 'from',
    s: 'subject',
    k: 'supported',
    t: 'to',
    v: 'via'
};

var parsers = {
    'to': parseAOR,
    'from': parseAOR,
    'contact': function(v, h) {
        if(v == '*')
            return v;
        else
            return parseMultiHeader(parseAOR, v, h);
    },
    'route': parseMultiHeader.bind(0, parseAorWithUri),
    'record-route': parseMultiHeader.bind(0, parseAorWithUri),
    'path': parseMultiHeader.bind(0, parseAorWithUri),
    'cseq': parseCSeq,
    'content-length': function(v) { return +v.s; },
    'via': parseMultiHeader.bind(0, parseVia),
    'www-authenticate': parseMultiHeader.bind(0, parseAuthHeader),
    'proxy-authenticate': parseMultiHeader.bind(0, parseAuthHeader),
    'authorization': parseMultiHeader.bind(0, parseAuthHeader),
    'proxy-authorization': parseMultiHeader.bind(0, parseAuthHeader),
    'authentication-info': parseAuthenticationInfoHeader,
    'refer-to': parseAOR
};

function parse(data) {
    data = data.split(/\r\n(?![ \t])/);

    if(data[0] === '')
        return;

    var m = {};

    if(!(parseResponse(data[0], m) || parseRequest(data[0], m)))
        return;

    m.headers = {};

    for(var i = 1; i < data.length; ++i) {
        var r = data[i].match(/^([\S]*?)\s*:\s*([\s\S]*)$/);
        if(!r) {
            return;
        }

        var name = unescape(r[1]).toLowerCase();
        name = compactForm[name] || name;

        m.headers[name] = (parsers[name] || parseGenericHeader)({s:r[2], i:0}, m.headers[name]);
    }

    return m;
}

function parseUri(s) {
    if(typeof s === 'object')
        return s;

    var re = /^(sips?):(?:([^\s>:@]+)(?::([^\s@>]+))?@)?([\w\-\.]+)(?::(\d+))?((?:;[^\s=\?>;]+(?:=[^\s?\;]+)?)*)(?:\?(([^\s&=>]+=[^\s&=>]+)(&[^\s&=>]+=[^\s&=>]+)*))?$/;

    var r = re.exec(s);

    if(r) {
        return {
            schema: r[1],
            user: r[2],
            password: r[3],
            host: r[4],
            port: +r[5],
            params: (r[6].match(/([^;=]+)(=([^;=]+))?/g) || [])
                .map(function(s) { return s.split('='); })
                .reduce(function(params, x) { params[x[0]]=x[1] || null; return params;}, {}),
            headers: ((r[7] || '').match(/[^&=]+=[^&=]+/g) || [])
                .map(function(s){ return s.split('='); })
                .reduce(function(params, x) { params[x[0]]=x[1]; return params; }, {})
        };
    }
}

exports.parseUri = parseUri;

function stringifyVersion(v) {
    return v || '2.0';
}

function stringifyParams(params) {
    var s = '';
    for(var n in params) {
            s += ';'+n+(params[n]?'='+params[n]:'');
    }

    return s;
}

function stringifyUri(uri) {
    if(typeof uri === 'string')
        return uri;

    var s = (uri.schema || 'sip') + ':';

    if(uri.user) {
        if(uri.password)
            s += uri.user + ':' + uri.password + '@';
        else
            s += uri.user + '@';
    }

    s += uri.host;

    if(uri.port)
        s += ':' + uri.port;

    if(uri.params)
        s += stringifyParams(uri.params);

    if(uri.headers) {
        var h = Object.keys(uri.headers).map(function(x){return x+'='+uri.headers[x];}).join('&');
        if(h.length)
            s += '?' + h;
    }
    return s;
}

exports.stringifyUri = stringifyUri;

function stringifyAOR(aor) {
    return (aor.name || '') + ' <' + stringifyUri(aor.uri) + '>'+stringifyParams(aor.params);
}

function stringifyAuthHeader(a) {
    var s = [];

    for(var n in a) {
        if(n !== 'scheme' && a[n] !== undefined) {
            s.push(n + '=' + a[n]);
        }
    }

    return a.scheme ? a.scheme + ' ' + s.join(',') : s.join(',');
}

exports.stringifyAuthHeader = stringifyAuthHeader;

var stringifiers = {
    via: function(h) {
        return h.map(function(via) {
            return 'Via: SIP/'+stringifyVersion(via.version)+'/'+via.protocol.toUpperCase()+' '+via.host+(via.port?':'+via.port:'')+stringifyParams(via.params)+'\r\n';
        }).join('');
    },
    to: function(h) {
        return 'To: '+stringifyAOR(h) + '\r\n';
      },
    from: function(h) {
        return 'From: '+stringifyAOR(h)+'\r\n';
    },
    contact: function(h) {
        return 'Contact: '+ ((h !== '*' && h.length) ? h.map(stringifyAOR).join(', ') : '*') + '\r\n';
    },
    route: function(h) {
        return h.length ? 'Route: ' + h.map(stringifyAOR).join(', ') + '\r\n' : '';
    },
    'record-route': function(h) {
        return h.length ? 'Record-Route: ' + h.map(stringifyAOR).join(', ') + '\r\n' : '';
    },
    'path': function(h) {
        return h.length ? 'Path: ' + h.map(stringifyAOR).join(', ') + '\r\n' : '';
    },
    cseq: function(cseq) {
        return 'CSeq: '+cseq.seq+' '+cseq.method+'\r\n';
    },
    'www-authenticate': function(h) {
        return h.map(function(x) { return 'WWW-Authenticate: '+stringifyAuthHeader(x)+'\r\n'; }).join('');
    },
    'proxy-authenticate': function(h) {
        return h.map(function(x) { return 'Proxy-Authenticate: '+stringifyAuthHeader(x)+'\r\n'; }).join('');
    },
    'authorization': function(h) {
        return h.map(function(x) { return 'Authorization: ' + stringifyAuthHeader(x) + '\r\n'; }).join('');
    },
    'proxy-authorization': function(h) {
        return h.map(function(x) { return 'Proxy-Authorization: ' + stringifyAuthHeader(x) + '\r\n'; }).join('');
    },
    'authentication-info': function(h) {
        return 'Authentication-Info: ' + stringifyAuthHeader(h) + '\r\n';
    },
    'refer-to': function(h) { return 'Refer-To: ' + stringifyAOR(h) + '\r\n'; }
};

function stringify(m) {
    var s;
    if(m.status) {
        s = 'SIP/' + stringifyVersion(m.version) + ' ' + m.status + ' ' + m.reason + '\r\n';
    }
    else {
        s = m.method + ' ' + stringifyUri(m.uri) + ' SIP/' + stringifyVersion(m.version) + '\r\n';
    }

    m.headers['content-length'] = (m.content || '').length;

    for(var n in m.headers) {
        if(typeof m.headers[n] === 'string' || !stringifiers[n])
            s += n + ': ' + m.headers[n] + '\r\n';
        else
            s += stringifiers[n](m.headers[n], n);
    }

    s += '\r\n';

    if(m.content)
        s += m.content;

    return s;
}

exports.stringify = stringify;

function makeResponse(rq, status, reason, extension) {
    var rs = {
        status: status,
        reason: reason || '',
        version: rq.version,
        headers: {
            via: rq.headers.via,
            to: rq.headers.to,
            from: rq.headers.from,
            'call-id': rq.headers['call-id'],
            cseq: rq.headers.cseq
        }
    };

    if(extension) {
        if(extension.headers) Object.keys(extension.headers).forEach(function(h) { rs.headers[h] = extension.headers[h]; });
        rs.content = extension.content;
    }

    return rs;
}

exports.makeResponse = makeResponse;

function clone(o, deep) {
    if(typeof o === 'object') {
        var r = Array.isArray(o) ? [] : {};
        Object.keys(o).forEach(function(k) { r[k] = deep ? clone(o[k], deep): o[k]; });
        return r;
    }

    return o;
}

exports.copyMessage = function(msg, deep) {
    if(deep) return clone(msg, true);

    var r = {
        uri: deep ? clone(msg.uri, deep) : msg.uri,
        method: msg.method,
        status: msg.status,
        reason: msg.reason,
        headers: clone(msg.headers, deep),
        content: msg.content
    };

    // always copy via array
    r.headers.via = clone(msg.headers.via);

    return r;
};

//TODO: have to check places where using this function...
function defaultPort(proto) {
    return proto.toUpperCase() === 'TLS' ? 5061 : 5060;
}

function makeStreamParser(onMessage) {
    var m;
    var r = '';

    function headers(data) {
        r += data;
        var a = r.match(/^\s*([\S\s]*?)\r\n\r\n([\S\s]*)$/);

        if(a) {
            r = a[2];
            m = parse(a[1]);

            if(m && m.headers['content-length'] !== undefined) {
                state = content;
                content('');
            }
        }
    }

    function content(data) {
        r += data;

        if(r.length >= m.headers['content-length']) {
            m.content = r.substring(0, m.headers['content-length']);

            onMessage(m);

            var s = r.substring(m.headers['content-length']);
            state = headers;
            r = '';
            headers(s);
        }
    }

    var state=headers;

    return function(data) { state(data); };
}
exports.makeStreamParser = makeStreamParser;

function parseMessage(s) {
    var r = s.toString('ascii').split('\r\n\r\n');
    if(r) {
        var m = parse(r[0]);

        if(m) {
            if(m.headers['content-length']) {
                var c = Math.max(0, Math.min(m.headers['content-length'], r[1].length));
                m.content = r[1].substring(0, c);
            }
            else {
                m.content = r[1];
            }

            return m;
        }
    }
}
exports.parse = parseMessage;

function checkMessage(msg) {
    return (msg.method || (msg.status >= 100 && msg.status <= 999)) &&
        msg.headers &&
        Array.isArray(msg.headers.via) &&
        msg.headers.via.length > 0 &&
        msg.headers['call-id'] &&
        msg.headers.to &&
        msg.headers.from &&
        msg.headers.cseq;
}

function makeStreamTransport(protocol, connect, createServer, callback, optCallbacks) {
    var remotes = Object.create(null);
    //var flows = Object.create(null);

    function init(stream, remote) {
        var remoteid = [remote.address, remote.port].join(),

            //a bit different between tcp and tls
            localAddr = stream.localAddress || stream.address().address,
            localPort = stream.localPort || stream.address().port,

            flow = {
                protocol: protocol,
                address: stream.remoteAddress,
                port: stream.remotePort,
                local: {
                    address: localAddr,
                    port: localPort
                }
            },
            refs = 0;

        stream.setEncoding('ascii');
        stream.on('data', makeStreamParser(function(m) {
            if (checkMessage(m)) {
                if (m.method) {
                    m.headers.via[0].params.received = remote.address;
                }
                callback(m, flow, stream);
            }
        }));

        stream.on('close',    function() {
            //if(flowid) delete flows[id];
            delete remotes[remoteid];
            if (optCallbacks.onClose) {
                optCallbacks.onClose(flow);
            }
        });
        stream.on('connect', function() {
            //flowid = [remoteid,stream.localAddress, stream.localPort].join();
            //flows[flowid] = remotes[remoteid];
        });

        stream.on('error',    function() {});

        stream.on('end',      function() {
            if(refs !== 0) stream.emit('error', new Error('remote peer disconnected'));
            stream.end();
        });

        stream.on('timeout',  function() { if(refs === 0) stream.end(); });
        stream.setTimeout(120 * 1000);
        stream.setKeepAlive(true, 20 * 1000);
        stream.setMaxListeners(10000);

        remotes[remoteid] = function(onError) {
            ++refs;
            if (onError) stream.on('error', onError);

            return {
                send: function(m) {
                    stream.write(stringify(m), 'ascii');
                },
                release: function() {
                    if(onError) stream.removeListener('error', onError);
                    if(--refs === 0) stream.emit('no_reference');
                },
                protocol: protocol,
                local: {
                    address: stream.localAddress,
                    port: stream.localPort
                }
            };
        };

        return remotes[remoteid];
    }

    var server = createServer(function(stream) {
        init(
            stream,
            {protocol: protocol, address: stream.remoteAddress, port: stream.remotePort}
        );
    });

    return {
        open: function(remote, onError, dontopen) {
            var id = [remote.address, remote.port].join();
            if (id in remotes) {
                return remotes[id](onError);
            }
            if (dontopen) {
                return null;
            }
            return init(connect(remote.port, remote.address), remote)(onError);
        },
        get: function(remote, onError) {
            var id = [remote.address, remote.port].join();
            if (id in remotes) {
                return remotes[id](onError);
            }
            else {
                return null;
            }
        },
        destroy: function() { server.close(); }
    };
}

function makeTlsTransport(options, callback, optCallbacks) {
    return makeStreamTransport(
        'TLS',
        function(port, host, callback) {
            return tls.connect(port, host, options.tls, callback);
        },
        function(callback) {
            var initObj = {
                key: fs.readFileSync(options.ssl.key),
                cert: fs.readFileSync(options.ssl.cert),
                honorCipherOrder: true
            };
            var server = tls.createServer(initObj, callback);
            server.listen(options.tls_port, options.bindAddress);
            return server;
        },
        callback,
        optCallbacks);
}

function makeTcpTransport(options, callback, optCallbacks) {
    return makeStreamTransport(
        'TCP',
        function(port, host, callback) {
            return net.connect(port, host, callback);
        },
        function(callback) {
            var server = net.createServer(callback);
            server.listen(options.udp_tcp_port, options.bindAddress);
            return server;
        },
        callback,
        optCallbacks);
}

function makeWsTransportInner(protocol, wsServerInitObj, callback, optCallbacks) {
    var flows = Object.create(null);

    var server = new WebSocket.Server(wsServerInitObj);
    server.on('connection', function(ws) {
        var remote = {
                address: ws._socket.remoteAddress,
                port: ws._socket.remotePort
            },
            local = {
                address: ws._socket.address().address,
                port: ws._socket.address().port
            },
            flow = {
                protocol: protocol,
                address: remote.address,
                port: remote.port,
                local: {
                    address: local.address,
                    port: local.port
                }
            },
            flowid = [remote.address, remote.port, local.address, local.port].join();

        flows[flowid] = ws;

        ws.on('close', function() {
            delete flows[flowid];
            if (optCallbacks.onClose) {
                optCallbacks.onClose(flow);
            }
        });

        ws.on('message', function(data) {
            var msg = parseMessage(data);
            if (msg && checkMessage(msg)) {
                callback(msg, flow);
            }
        });
    });

    function get(flow, onError) {
        myLogger.debug("wsTranport#get");
        var ws = flows[[flow.address, flow.port, flow.local.address, flow.local.port].join()];
        if (ws) {
            return {
                send: function(m) {
                    ws.send(stringify(m));
                },
                release: function() {},
                protocol: protocol,
                local: {
                    protocol: protocol,
                    address: ws._socket.address().address,
                    port: ws._socket.address().port
                },
            };
        }
        else {
            return null;
        }
    }

    return {
        get: get,
        open: get,
        destroy: function() { server.close(); }
    };
}

function makeWsTransport(options, callback, optCallbacks) {
    var wsServerInitObj = {
        port: options.ws_port,
        host: options.bindAddress
    };
    return makeWsTransportInner('WS', wsServerInitObj, callback, optCallbacks);
}

function makeWssTransport(options, callback, optCallbacks) {
    var dummyReqHandler = function(req, res) {
        res.writeHead(404);
        res.end();
    };
    var srv = https.createServer({
        key: fs.readFileSync(options.ssl.key),
        cert: fs.readFileSync(options.ssl.cert)
    }, dummyReqHandler).listen(options.wss_port, options.bindAddress);

    var wsServerInitObj = {server: srv};
    return makeWsTransportInner('WSS', wsServerInitObj, callback, optCallbacks);
}

function makeUdpTransport(options, callback, optCallbacks) {
    var bindAddress = options.bindAddress;
    var bindPort = options.udp_tcp_port;

    function onMessage(data, rInfo) {
        myLogger.debug("sip#makeUdpTransport onMessage");
        var msg = parseMessage(data),
            flow = {
                protocol: 'UDP',
                address: rInfo.address,
                port: rInfo.port,
                local: {
                    address: options.publicAddress,
                    port: bindPort
                }
            };

        if (msg && checkMessage(msg)) {
            if (msg.method) {
                msg.headers.via[0].params.received = rInfo.address;
                if (msg.headers.via[0].params.hasOwnProperty('rport')) {
                    msg.headers.via[0].params.rport = rInfo.port;
                }
            }
            callback(msg, flow);
        }
    }

    var socket = dgram.createSocket(net.isIPv6(bindAddress) ? 'udp6' : 'udp4', onMessage);
    socket.bind(bindPort, bindAddress);

    function open(remote, error) {
        return {
            send: function(m) {
                var s = stringify(m);
                socket.send(new Buffer(s, 'ascii'), 0, s.length, remote.port, remote.address);
            },
            protocol: 'UDP',
            release : function() {},
            local: {
                address: bindAddress,
                port: bindPort
            }
        };
    }

    return {
        open: open,
        get: open,
        destroy: function() { socket.close(); }
    };
}

function makeTransport(options, onMsgCallback, optCallbacks) {
    var protocols = {};

    var onMsgCallbackWrap = onMsgCallback;
    if(options.logger && options.logger.recv) {
        onMsgCallbackWrap = function(m, remote, stream) {
            options.logger.recv(m, remote);
            onMsgCallback(m, remote, stream);
        };
    }

    if (options.udp === undefined || options.udp) {
        protocols.UDP = makeUdpTransport(options, onMsgCallbackWrap, optCallbacks);
    }
    if (options.tcp === undefined || options.tcp) {
        protocols.TCP = makeTcpTransport(options, onMsgCallbackWrap, optCallbacks);
    }
    if (options.tls) {
        protocols.TLS = makeTlsTransport(options, onMsgCallbackWrap, optCallbacks);
    }
    if (options.ws_port && WebSocket) {
        protocols.WS = makeWsTransport(options, onMsgCallbackWrap, optCallbacks);
    }
    if (options.wss_port && WebSocket) {
        protocols.WSS = makeWssTransport(options, onMsgCallbackWrap, optCallbacks);
    }

    function wrap(transportObj, target) {
        return Object.create(transportObj, {send: {value: function(m) {
            //do the wrap
            if (m.method) {
                //add "via" for this host
                m.headers.via[0].host = options.publicAddress ||
                                        options.hostname ||
                                        os.hostname();
                m.headers.via[0].port = transportObj.local.port;
                m.headers.via[0].protocol = this.protocol;

                if (this.protocol === 'UDP' &&
                    (!options.hasOwnProperty('rport') || options.rport)
                ) {
                    m.headers.via[0].params.rport = null;
                }
            }

            //log
            var logSend = (options.logger && options.logger.send) || function() {};
            logSend(m, target);

            //send
            try {
                transportObj.send(m);
            }
            catch (e) {
                var errorLog = (options.logger && options.logger.error) || function() {};
                errorLog(e);
            }
        }}});
    }

    return {
        open: function(target, error) {
            var protocol = target.protocol.toUpperCase();
            var transportObj = protocols[protocol].open(target, error);
            if (!transportObj) {
                throw new Error('transport not found');
            }
            return wrap(transportObj, target);
        },
        get: function(target, error) {
            var protocol = target.protocol.toUpperCase();
            var transportObj = protocols[protocol].get(target, error);
            if (!transportObj) {
                throw new Error('transport not found');
            }
            return wrap(transportObj, target);
        },
        send: function(target, message) {
            var cn = this.open(target);
            try {
                cn.send(message);
            }
            finally {
                cn.release();
            }
        },
        destroy: function() {
            var protos = protocols;
            protocols = [];
            Object.keys(protos).forEach(function(key) { protos[key].destroy(); });
        },
    };
}

exports.makeTransport = makeTransport;

function makeWellBehavingResolver(resolve) {
    var outstanding = Object.create(null);

    return function(name, cb) {
        if(outstanding[name]) {
            outstanding[name].push(cb);
        }
        else {
            outstanding[name] = [cb];

            resolve(name, function() {
                var o = outstanding[name];
                delete outstanding[name];
                var args = arguments;
                o.forEach(function(x) { x.apply(null, args); });
            });
        }
    };
}

var resolveSrv = makeWellBehavingResolver(dns.resolveSrv);
var resolve4 = makeWellBehavingResolver(dns.resolve4);
var resolve6 = makeWellBehavingResolver(dns.resolve6);

function resolve(uri, callback, myHostname) {
    myLogger.debug("sip#resolve");
    myLogger.debug(util.inspect(uri));
    if (net.isIP(uri.host)) {
        //prevent from sending to myself
        if (uri.host === myHostname) {
            return callback([]);
        }
        else {
            var protocol = uri.params.transport || 'UDP';
            return callback([{protocol: protocol, address: uri.host, port: uri.port || defaultPort(protocol)}]);
        }
    }

    function resolve46(host, cb) {
        resolve4(host, function(e4, a4) {
            resolve6(host, function(e6, a6) {
                if((a4 || a6) && (a4 || a6).length)
                    cb(null, (a4 || []).concat(a6 || []));
                else
                    cb(e4 || e6, []);
            });
        });
    }

    var protocols = [];
    if (uri.port) {
        protocols = uri.params.protocol ? [uri.params.protocol] : ['UDP', 'TCP', 'TLS'];

        resolve46(uri.host, function(err, address) {
            address = (address || []).map(function(x) {
                return protocols.map(function(p) {
                    return {
                        protocol: p,
                        address: x,
                        port: uri.port || defaultPort(p)
                    };
                });
            }).reduce(function(arr,v) {
                return arr.concat(v);
            }, []);
            callback(address);
        });
    }
    else {
        protocols = uri.params.protocol ? [uri.params.protocol] : ['tcp', 'udp', 'tls'];

        var n = protocols.length;
        var addresses = [];

        protocols.forEach(function(proto) {
            resolveSrv('_sip._'+proto+'.'+uri.host, function(e, r) {
                --n;

                if(Array.isArray(r)) {
                    n += r.length;
                    r.forEach(function(srv) {
                        resolve46(srv.name, function(e, r) {
                            addresses = addresses.concat((r||[]).map(function(a) { return {protocol: proto, address: a, port: srv.port};}));

                            if((--n)===0) // all outstanding requests has completed
                                callback(addresses);
                        });
                    });
                }
                else if(0 === n) {
                    if(addresses.length) {
                        callback(addresses);
                    }
                    else {
                        // all srv requests failed
                        resolve46(uri.host, function(err, address) {
                            address = (address || []).map(function(x) { return protocols.map(function(p) { return { protocol: p, address: x, port: uri.port || defaultPort(p)};});})
                                .reduce(function(arr,v) { return arr.concat(v); }, []);
                            callback(address);
                        });
                    }
                }
            });
        });
    }
}

exports.resolve = resolve;

//transaction layer
function generateBranch() {
    return ['z9hG4bK', Math.round(Math.random()*1000000)].join('');
}

exports.generateBranch = generateBranch;

function makeSM() {
    var state;

    return {
        enter: function(newstate) {
            if(state && state.leave)
                state.leave();

            state = newstate;
            Array.prototype.shift.apply(arguments);
            if(state.enter)
                state.enter.apply(this, arguments);
        },
        signal: function(s) {
            if(state && state[s])
                state[Array.prototype.shift.apply(arguments)].apply(state, arguments);
        }
    };
}

function createInviteServerTransaction(transport, cleanup) {
    myLogger.debug("createInviteServerTransaction");
    var sm = makeSM();
    var rs;

    var proceeding = {
        message: function() {
            if(rs) transport(rs);
        },
        send: function(message) {
            rs = message;

            if(message.status >= 300)
                sm.enter(completed);
            else if(message.status >= 200)
                sm.enter(accepted);

            transport(rs);
        }
    };

    var g, h;
    var completed = {
        enter: function () {
            g = setTimeout(function retry(t) {
                g = setTimeout(retry, t*2, t*2);
                transport(rs);
            }, 500, 500);
            h = setTimeout(sm.enter.bind(sm, terminated), 32000);
        },
        leave: function() {
            clearTimeout(g);
            clearTimeout(h);
        },
        message: function(m) {
            if(m.method === 'ACK')
                sm.enter(confirmed);
            else
                transport(rs);
        }
    };

    var timer_i;
    var confirmed = {
        enter: function() { timer_i = setTimeout(sm.enter.bind(sm, terminated), 5000);},
        leave: function() { clearTimeout(timer_i); }
    };

    var l;
    var accepted = {
        enter: function() { l = setTimeout(sm.enter.bind(sm, terminated), 32000);},
        leave: function() { clearTimeout(l); },
        send: function(m) {
            rs = m;
            transport(rs);
        }
    };

    var terminated = {enter: cleanup};

    sm.enter(proceeding);

    return {send: sm.signal.bind(sm, 'send'), message: sm.signal.bind(sm,'message'), shutdown: function() { sm.enter(terminated); }};
}

function createServerTransaction(transport, cleanup) {
    myLogger.debug("createServerTransaction");
    var sm = makeSM();
    var rs;

    var trying = {
        message: function() { if(rs) transport(rs); },
        send: function(m) {
            rs = m;
            transport(m);
            if(m.status >= 200) sm.enter(completed);
        }
    };

    var j;
    var completed = {
        message: function() { transport(rs); },
        enter: function() { j = setTimeout(function() { sm.enter(terminated); }, 32000); },
        leave: function() { clearTimeout(j); }
    };

    var terminated = {enter: cleanup};

    sm.enter(trying);

    return {send: sm.signal.bind(sm, 'send'), message: sm.signal.bind(sm, 'message'), shutdown: function() { sm.enter(terminated); }};
}

function createInviteClientTransaction(rq, transport, tu, cleanup, options) {
    myLogger.debug("createInviteClientTransaction");
    var sm = makeSM();

    var a, b;
    var calling = {
        enter: function() {
            transport(rq);

            if (!transport.reliable) {
                a = setTimeout(function resend(t) {
                    transport(rq);
                    a = setTimeout(resend, t*2, t*2);
                }, 500, 500);
            }

            b = setTimeout(function() {
                tu(makeResponse(rq, 503, 'Service Unavailable'));
                sm.enter(terminated);
            }, 32000);

            if (options && options.inviteCallingCallback) {
                options.inviteCallingCallback(rq);
            }
        },
        leave: function() {
            clearTimeout(a);
            clearTimeout(b);
        },
        message: function(message) {
            tu(message);

            if(message.status < 200)
                sm.enter(proceeding);
            else if(message.status < 300)
                  sm.enter(accepted);
            else
                sm.enter(completed, message);
        }
    };

    var proceeding = {
        message: function(message) {
            tu(message);

            if(message.status >= 300)
                sm.enter(completed, message);
            else if(message.status >= 200)
                sm.enter(accepted);
        }
    };

    var ack = {
        method: 'ACK',
        uri: rq.uri,
        headers: {
            from: rq.headers.from,
            cseq: {method: 'ACK', seq: rq.headers.cseq.seq},
            'call-id': rq.headers['call-id'],
            via: [rq.headers.via[0]],
            'max-forwards': (options && options['max-forwards']) || 70
        }
    };

    var d;
    var completed = {
        enter: function(rs) {
            ack.headers.to=rs.headers.to;
            transport(ack);
            d = setTimeout(sm.enter.bind(sm, terminated), 32000);
            if (options && options.inviteCompletedCallback) {
                options.inviteCompletedCallback(rq, rs);
            }
        },
        leave: function() { clearTimeout(d); },
        message: function(message, remote) {
            if(remote) transport(ack);  // we don't want to ack internally generated messages
        }
    };

    var timer_m;
    var accepted = {
        enter: function() {
            timer_m = setTimeout(function() { sm.enter(terminated); }, 32000);
            if (options && options.inviteAcceptedCallback) {
                options.inviteAcceptedCallback(rq);
            }
        },
        leave: function() { clearTimeout(timer_m); },
        message: function(m) {
            if(m.status >= 200 && m.status <= 299)
                tu(m);
        }
    };

    var terminated = {enter: cleanup};

    sm.enter(calling);

    return {message: sm.signal.bind(sm, 'message'), shutdown: function() { sm.enter(terminated); }};
}

function createClientTransaction(rq, transport, tu, cleanup) {
    myLogger.debug("createClientTransaction");
    assert.ok(rq.method !== 'INVITE');

    var sm = makeSM();

    var e, f;
    var trying = {
        enter: function() {
            transport(rq);
            if (!transport.reliable) {
                e = setTimeout(function() {
                    sm.signal('timerE', 500);
                }, 500);
            }
            f = setTimeout(function() { sm.signal('timerF'); }, 32000);
        },
        leave: function() {
            clearTimeout(e);
            clearTimeout(f);
        },
        message: function(message, remote) {
            if(message.status >= 200)
                sm.enter(completed);
            else
                sm.enter(proceeding);
            tu(message);
        },
        timerE: function(t) {
            transport(rq);
            e = setTimeout(function() { sm.signal('timerE', t*2); }, t*2);
        },
        timerF: function() {
            tu(makeResponse(rq, 503, 'Service Unavailable'));
            sm.enter(terminated);
        }
    };

    var proceeding = {
        message: function(message, remote) {
            if(message.status >= 200)
                sm.enter(completed);
            tu(message);
        }
    };

    var k;
    var completed = {
        enter: function() { k = setTimeout(function() { sm.enter(terminated); }, 5000); },
        leave: function() { clearTimeout(k); }
    };

    var terminated = {enter: cleanup};

    sm.enter(trying);

    return {message: sm.signal.bind(sm, 'message'), shutdown: function() { sm.enter(terminated); }};
}

function makeTransactionId(m) {
    if(m.method === 'ACK')
        return ['INVITE', m.headers['call-id'], m.headers.via[0].params.branch].join();
    return [m.headers.cseq.method, m.headers['call-id'], m.headers.via[0].params.branch].join();
}

function makeTransactionLayer(options, transport) {
    var server_transactions = Object.create(null);
    var client_transactions = Object.create(null);

    return {
        createServerTransaction: function(rq, cn) {
            myLogger.debug("makeTransactionLayer#createServerTransaction");
            var id = makeTransactionId(rq);

            server_transactions[id] = (rq.method === 'INVITE' ? createInviteServerTransaction : createServerTransaction)(
                cn.send.bind(cn),
                function() {
                    delete server_transactions[id];
                    cn.release();
                }
            );
            return server_transactions[id];
        },
        createClientTransaction: function(connection, rq, callback) {
            myLogger.debug("makeTransactionLayer#createClientTransaction");
            if (rq.method !== 'CANCEL') {
                rq.headers.via[0].params.branch = generateBranch();
            }

            if (typeof rq.headers.cseq !== 'object') {
                rq.headers.cseq = parseCSeq({s: rq.headers.cseq, i:0});
            }

            var send = connection.send.bind(connection);
            send.reliable = connection.protocol.toUpperCase() !== 'UDP';

            var id = makeTransactionId(rq);
            client_transactions[id] = (rq.method === 'INVITE' ? createInviteClientTransaction : createClientTransaction)(
                rq,
                send,
                callback,
                function() {
                    delete client_transactions[id];
                    connection.release();
                },
                options
            );
            return client_transactions[id];
        },
        getServer: function(m) {
            return server_transactions[makeTransactionId(m)];
        },
        getClient: function(m) {
            return client_transactions[makeTransactionId(m)];
        },
        destroy: function() {
            Object.keys(client_transactions).forEach(function(x) { client_transactions[x].shutdown(); });
            Object.keys(server_transactions).forEach(function(x) { server_transactions[x].shutdown(); });
        }
    };
}

exports.makeTransactionLayer = makeTransactionLayer;

function sequentialSearch(transaction, transport, addresses, rq, callback) {
    myLogger.debug("sip#sequentialSearch");

    var createClientTransactionFunc = transaction.createClientTransaction.bind(transaction);
    var connectFunc = transport.open.bind(transport);

    if (rq.method !== 'CANCEL') {
        if(!rq.headers.via) rq.headers.via = [];
        rq.headers.via.unshift({params:{}});
    }

    var onresponse;
    function next() {
        onresponse = searching;

        if (addresses.length > 0) {
            try {
                var address = addresses.shift();
                var client = createClientTransactionFunc(
                    connectFunc(
                        address,
                        function() { client.message(makeResponse(rq, 503, 'Service Unavailable'));}
                    ),
                    rq,
                    function() { onresponse.apply(null, arguments); }
                );
            }
            catch(e) {
                onresponse(address.local ?
                        makeResponse(rq, 430, 'Flow Failed') :
                        makeResponse(rq, 503, 'Service Unavailable')
                );
            }
        }
        else {
            onresponse(makeResponse(rq, 404, 'Not Found'));
        }
    }

    function searching(rs) {
        if(rs.status === 503)
            return next();
        else if(rs.status > 100)
            onresponse = callback;

        callback(rs);
    }

    next();
}

exports.create = function(options, onMsgCallback, optCallbacks) {
    var errorLog = (options.logger && options.logger.error) || function() {};

    var transport = makeTransport(options, function(m, remote) {
        myLogger.debug("makeTransport onMessage. \nfrom = " + util.inspect(remote));
        try {
            var t = m.method ? transaction.getServer(m) : transaction.getClient(m);

            //no transaction yet. start one if needed.
            if (!t) {
                if(m.method && m.method !== 'ACK') {
                    var transCon = transport.get(remote);
                    t = transaction.createServerTransaction(m, transCon);
                    try {
                        onMsgCallback(m,remote);
                    } catch(e) {
                        myLogger.error("transport - Internal Server Error");
                        myLogger.error(util.inspect(m, {depth:null}));
                        t.send(makeResponse(m, '500', 'Internal Server Error'));
                        throw e;
                    }
                }
                else if(m.method === 'ACK') {
                    onMsgCallback(m,remote);
                }
            }
            else {
                if (t.message) {
                    t.message(m, remote);
                }
            }
        }
        catch(e) {
            errorLog(e);
        }
    }, optCallbacks);

    var transaction = makeTransactionLayer(options, transport.open.bind(transport));
    var hostname = options.publicAddress || options.hostname || os.hostname();
    //see http://tools.ietf.org/html/draft-ietf-sip-outbound-16#section-5.2
    var rbytes = crypto.randomBytes(20);

    function encodeFlowToken(flow) {
        var s = [flow.protocol, flow.address, flow.port, flow.local.address, flow.local.port].join();
        var h = crypto.createHmac('sha1', rbytes);
        h.update(s);
        return toBase64([h.digest('base64'), s].join());
    }

    function decodeFlowToken(token) {
        var s = (new Buffer(token, 'base64')).toString('ascii').split(',');
        if (s.length != 6) return undefined;

        var h = crypto.createHmac('sha1', rbytes);
        h.update([s[1], s[2], +s[3], s[4], +s[5]].join());

        var flow = {
            protocol: s[1],
            address: s[2],
            port: +s[3],
            local: {address: s[4], port: +s[5]}
        };

        return h.digest('base64') === s[0] ? flow : undefined;
    }

    return {
        send: function(m, msgPath, callback) {
            myLogger.debug("sip#exports.send");
            //responding to client
            if (m.method === undefined) {
                var t = transaction.getServer(m);
                if (t && t.send) {
                    try {
                        t.send(m);
                    }
                    catch(e) {
                        errorLog(e);
                    }
                    finally {
                    }
                }
            }
            //forwarding request from client
            else {
                var hop = parseUri(m.uri);
                var isHopTakenFromRoute = false;

                if (typeof m.headers.route === 'string') {
                    m.headers.route = parsers.route({s: m.headers.route, i:0});
                }

                if (m.headers.route && m.headers.route.length > 0) {
                    hop = parseUri(m.headers.route[0].uri);
                    isHopTakenFromRoute = true;
                    /*
                      TODO:
                      strictly speaking, IF clause should only be true when
                      hop.host === hostname
                      AND (
                        isNaN(hop.port)
                        OR
                        portIsAssociatedWithThisProxy(hop.port, protocol, options)
                      ).
                      The implementation of portisassociatedwiththisproxy() should
                      be trivial. But where should we get the protocol from?
                     */
                    if (hop.host === hostname) {
                        m.headers.route.shift();
                    }
                    else if (hop.params.lr === undefined) {
                        m.headers.route.shift();
                        m.headers.route.push({uri: m.uri});
                        m.uri = hop;
                    }
                }

                var _send = function(addresses) {
                    myLogger.debug("sip#export._send");
                    myLogger.debug(util.inspect(addresses));
                    if (m.method === 'ACK') {
                        if(addresses.length === 0) {
                            errorLog(new Error("ACK: couldn't resolve " + stringifyUri(m.uri)));
                            return;
                        }

                        var cn = transport.open(addresses[0], errorLog);
                        try {
                            cn.send(m);
                        }
                        catch(e) {
                            errorLog(e);
                        }
                        finally {
                            cn.release();
                        }
                    }
                    else {
                        sequentialSearch(
                            transaction,
                            transport,
                            addresses,
                            m,
                            callback || function(){}
                        );
                    }
                };

                if (isHopTakenFromRoute) {
                    var flow = decodeFlowToken(hop.user);
                    _send(flow ? [flow] : []);
                }
                else if (msgPath) {
                    var addresses = [{
                        protocol: msgPath.dstFlow.protocol,
                        address: msgPath.dstFlow.address,
                        port: msgPath.dstFlow.port,
                        local: {
                            address: msgPath.dstFlow.local.address,
                            port: msgPath.dstFlow.local.port,
                        }
                    }];
                    _send(addresses);
                }
                //this only cares about the remote destination.
                else {
                    resolve(hop, _send, hostname);
                }
            }
        },
        encodeFlowUri: function(flow) {
            var protocol = flow.protocol.toUpperCase(),
                schema = 'sip',
                params = {};

            if (protocol === 'TLS') {
                params.transport = 'tls';
            }
            else if (protocol === 'TCP') {
                params.transport = 'tcp';
            }

            return {
                schema: schema,
                user: encodeFlowToken(flow),
                host: hostname,
                port: flow.local.port,
                params: params
            };
        },
        decodeFlowUri: function(uri) {
            uri = parseUri(uri);
            return uri.host === hostname ? decodeFlowToken(uri.user) : undefined;
        },
        isFlowUri: function(uri) {
            return !!!decodeFlowUri(uri);
        },
        hostname: function() { return hostname; },
        destroy: function() {
            transaction.destroy();
            transport.destroy();
        }
    };
};

exports.start = function(options, onMsgCallback, optCallbacks) {
    if (options.sipCoreLogger) {
        myLogger = options.sipCoreLogger;
    }

    var r = exports.create(options, onMsgCallback, optCallbacks);

    exports.send = r.send;
    exports.stop = r.destroy;
    exports.encodeFlowUri = r.encodeFlowUri;
    exports.decodeFlowUri = r.decodeFlowUri;
    exports.isFlowUri = r.isFlowUri;
    exports.hostname = r.hostname;
};

