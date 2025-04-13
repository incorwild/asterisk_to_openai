// Import required Node.js modules
const ari = require('ari-client'); // Asterisk REST Interface client
const WebSocket = require('ws'); // WebSocket library (будет использоваться только для обратной совместимости)
const fs = require('fs'); // File system module for saving audio files
const dgram = require('dgram'); // UDP datagram for RTP audio streaming
const winston = require('winston'); // Logging library
const chalk = require('chalk'); // Colorizes console output
const async = require('async'); // Async utilities (used for RTP queue)
const axios = require('axios'); // HTTP client для запросов к ElevenLabs API
require('dotenv').config(); // Loads environment variables from .env file

// Configuration constants loaded from environment variables or defaults
const ARI_URL = process.env.ARI_URL || 'http://127.0.0.1:8088'; // Asterisk ARI endpoint
const BIND_URL = process.env.BIND_URL || '0.0.0.0'; // Bind address for RTP receiver
const ARI_USER = process.env.ARI_USER || 'asterisk'; // ARI username
const ARI_PASS = process.env.ARI_PASS || 'asterisk'; // ARI password
const ARI_APP = process.env.ARI_APP || 'stasis_app'; // Stasis application name
// ElevenLabs API configuration
const ELEVENLABS_API_KEY = process.env.ELEVENLABS_API_KEY; // ElevenLabs API key from .env
const ELEVENLABS_API_URL = process.env.ELEVENLABS_API_URL || 'https://api.elevenlabs.io/v1'; // ElevenLabs API base URL
const ELEVENLABS_VOICE_ID = process.env.ELEVENLABS_VOICE_ID || '21m00Tcm4TlvDq8ikWAM'; // ElevenLabs voice ID (default: Rachel - доступна в бесплатной версии)
const ELEVENLABS_MODEL_ID = process.env.ELEVENLABS_MODEL_ID || 'eleven_monolingual_v1'; // ElevenLabs model ID
const ELEVENLABS_OUTPUT_FORMAT = process.env.ELEVENLABS_OUTPUT_FORMAT || 'pcm_16000'; // Output format (pcm_16000, pcm_22050, pcm_24000, mp3)
// Outbound call configuration
const DEFAULT_CALLER_ID = process.env.DEFAULT_CALLER_ID || 'ElevenLabs <9000>'; // Default caller ID for outbound calls
const DEFAULT_EXTENSION = process.env.DEFAULT_EXTENSION || 'from-internal'; // Default extension for outbound calls
const DEFAULT_CONTEXT = process.env.DEFAULT_CONTEXT || 'from-internal'; // Default context for outbound calls
const DEFAULT_PRIORITY = process.env.DEFAULT_PRIORITY ? parseInt(process.env.DEFAULT_PRIORITY) : 1; // Default priority for outbound calls
const RTP_PORT = process.env.LOCAL_RTP_PORT ? parseInt(process.env.LOCAL_RTP_PORT) : 12000; // Local port for RTP audio reception
const MAX_CALL_DURATION = process.env.MAX_CALL_DURATION ? parseInt(process.env.MAX_CALL_DURATION) : 300000; // Max call duration in ms (default: 5 min)
const RTP_QUEUE_CONCURRENCY = parseInt(process.env.RTP_QUEUE_CONCURRENCY) || 50; // Concurrent RTP packet sends
const LOG_RTP_EVERY_N_PACKETS = parseInt(process.env.LOG_RTP_EVERY_N_PACKETS) || 100; // Log RTP stats every N packets
const ENABLE_RTP_LOGGING = process.env.ENABLE_RTP_LOGGING === 'true'; // Enable detailed RTP logging
const ENABLE_AUDIO_RECORDING = process.env.ENABLE_AUDIO_RECORDING === 'true'; // Управляет сохранением аудио файлов .raw и .wav
const VAD_THRESHOLD = process.env.VAD_THRESHOLD ? parseFloat(process.env.VAD_THRESHOLD) : 0.1; // Voice Activity Detection threshold
const VAD_PREFIX_PADDING_MS = process.env.VAD_PREFIX_PADDING_MS ? parseInt(process.env.VAD_PREFIX_PADDING_MS) : 300; // VAD prefix padding in ms
const VAD_SILENCE_DURATION_MS = process.env.VAD_SILENCE_DURATION_MS ? parseInt(process.env.VAD_SILENCE_DURATION_MS) : 500; // VAD silence duration in ms
const TARGET_RMS = 0.15; // Target Root Mean Square for audio normalization
const MIN_RMS = 0.001; // Minimum RMS to apply gain

// Счетчики для логирования событий
let sentEventCounter = 0; // Отслеживает отправленные события
let receivedEventCounter = -1; // Отслеживает полученные события

// Configure Winston logger with timestamp and colorized output
const logger = winston.createLogger({
  level: 'info', // Log level
  format: winston.format.combine(
    winston.format.timestamp(), // Add timestamp to logs
    winston.format.printf(({ timestamp, level, message }) => {
      const [origin] = message.split(' ', 1); // Extract message origin (Client/Server)
      let counter;
      let coloredMessage;
      if (origin === '[Client]') {
        counter = `C-${sentEventCounter.toString().padStart(4, '0')}`; // Client event counter
        sentEventCounter++;
        coloredMessage = chalk.cyanBright(message); // Cyan for client messages
      } else if (origin === '[Server]') {
        counter = `S-${receivedEventCounter.toString().padStart(4, '0')}`; // Server event counter
        receivedEventCounter++;
        coloredMessage = chalk.yellowBright(message); // Yellow for server messages
      } else {
        counter = 'N/A'; // No counter for general logs
        coloredMessage = chalk.gray(message); // Gray for general logs
      }
      return `${counter} | ${timestamp} [${level.toUpperCase()}] ${coloredMessage}`; // Formatted log line
    })
  ),
  transports: [new winston.transports.Console()] // Output logs to console
});

// Функции для логирования событий
const logClient = (msg) => logger.info(`[Client] ${msg}`); // Логирование исходящих событий
const logServer = (msg) => logger.info(`[Server] ${msg}`); // Логирование входящих событий

// Maps to track channel states and audio buffers
const extMap = new Map(); // Maps ExternalMedia channels to their bridges and SIP channels
const sipMap = new Map(); // Maps SIP channels to their WebSocket and bridge data
const rtpSender = dgram.createSocket('udp4'); // Single UDP socket for sending RTP packets
let rtpReceiver = dgram.createSocket('udp4'); // UDP socket for receiving RTP packets
let ariClient; // ARI client instance

const audioFromAsteriskMap = new Map(); // Buffers audio received from Asterisk
const audioToTTSMap = new Map(); // Буферизирует аудио для TTS сервиса
const amplificationLogFrequency = new Map(); // Tracks last amplification log time per channel
const rmsLogFrequency = new Map(); // Tracks last RMS log time per channel
const rtpSentStats = new Map(); // Tracks RTP stats per channel

// Add an ExternalMedia channel to a bridge with retry logic
async function addExtToBridge(client, channel, bridgeId, retries = 5, delay = 500) {
  try {
    const bridge = await client.bridges.get({ bridgeId }); // Fetch bridge by ID
    if (!bridge) throw new Error('Bridge not found');
    await bridge.addChannel({ channel: channel.id }); // Add channel to bridge
    logger.info(`ExternalMedia channel ${channel.id} added to bridge ${bridgeId}`);
  } catch (err) {
    if (retries) {
      logger.info(`Retrying to add ExternalMedia channel ${channel.id} to bridge ${bridgeId} (${retries} attempts remaining)`);
      await new Promise(r => setTimeout(r, delay)); // Wait before retrying
      return addExtToBridge(client, channel, bridgeId, retries - 1, delay); // Recursive retry
    }
    logger.error(`Error adding ExternalMedia channel ${channel.id} to bridge ${bridgeId}: ${err.message}`);
  }
}

// Start the RTP receiver to listen for audio from Asterisk
function startRTPReceiver() {
  logger.info(`Запуск функции startRTPReceiver()`);
  if (!rtpReceiver) {
    logger.error(`КРИТИЧЕСКАЯ ОШИБКА: rtpReceiver не инициализирован! Создаем новый сокет.`);
    rtpReceiver = dgram.createSocket('udp4');
  }
  logger.info(`Состояние сокета: ${JSON.stringify({
    initialized: rtpReceiver !== null,
    bound: rtpReceiver._bindState !== undefined ? rtpReceiver._bindState : 'неизвестно'
  })}`);

  let packetCount = 0; // Count of received RTP packets
  let totalBytes = 0; // Total bytes received
  let startTime = Date.now(); // Start time for rate calculation
  const audioBuffers = new Map(); // Temporary audio buffers per channel
  const BUFFER_INTERVAL_MS = 200; // Interval to process audio chunks (ms)

  rtpReceiver.on('listening', () => {
    const address = rtpReceiver.address();
    logger.info(`RTP Receiver listening on ${address.address}:${address.port}`);
    // Вывод информации о состоянии сокета для отладки
    logger.info(`RTP сокет: ${rtpReceiver ? 'создан' : 'не создан'}, настройки привязки: ${JSON.stringify({ port: RTP_PORT, address: BIND_URL })}`);
  });

  // Handle incoming RTP packets
  rtpReceiver.on('message', (msg, rinfo) => {
    logger.info(`!!! ПОЛУЧЕН ПАКЕТ RTP !!! от ${rinfo.address}:${rinfo.port} | Размер: ${msg.length} байт`);
    logger.info(`Received RTP packet from ${rinfo.address}:${rinfo.port} | Size: ${msg.length} bytes`);
    packetCount++;
    totalBytes += msg.length;
    if (packetCount >= 100) { // Log stats every 100 packets
      const currentTime = Date.now();
      const duration = (currentTime - startTime) / 1000;
      const rate = (packetCount / duration).toFixed(2);
      logger.info(`Received ${packetCount} RTP packets from ${rinfo.address}:${rinfo.port}, total bytes: ${totalBytes}, rate: ${rate} packets/s`);
      packetCount = 0;
      totalBytes = 0;
      startTime = currentTime;
    }

    // Find channel ID based on RTP source
    let channelId = [...sipMap.entries()].find(([_, data]) => data.rtpSource && data.rtpSource.address === rinfo.address && data.rtpSource.port === rinfo.port)?.[0];
    if (!channelId && sipMap.size > 0) {
      channelId = Array.from(sipMap.keys())[0];
      const data = sipMap.get(channelId);
      if (data && !data.rtpSource) {
        data.rtpSource = { address: rinfo.address, port: rinfo.port };
        logger.info(`AUTO-FIX: Assigned RTP source ${rinfo.address}:${rinfo.port} to channel ${channelId}`);
      }
    }

    if (channelId) {
      const muLawData = msg.slice(12); // Extract μ-law payload (skip RTP header)
      if (!audioFromAsteriskMap.has(channelId)) audioFromAsteriskMap.set(channelId, Buffer.alloc(0));
      audioFromAsteriskMap.set(channelId, Buffer.concat([audioFromAsteriskMap.get(channelId), muLawData])); // Append to Asterisk audio buffer

      const pcmBuffer24kHz = muLawToPcm24kHz(muLawData, channelId); // Convert to PCM 24kHz
      if (!audioBuffers.has(channelId)) audioBuffers.set(channelId, Buffer.alloc(0));
      audioBuffers.set(channelId, Buffer.concat([audioBuffers.get(channelId), pcmBuffer24kHz])); // Append to temporary buffer

      // Интервал для обработки входящего аудио
      if (!sipMap.get(channelId).sendTimeout) {
        sipMap.get(channelId).sendTimeout = setInterval(() => {
          const buffer = audioBuffers.get(channelId);
          if (buffer && buffer.length > 0) {
            let sumSquares = 0;
            for (let i = 0; i < buffer.length / 2; i++) { // Calculate RMS
              const sample = buffer.readInt16LE(i * 2);
              sumSquares += sample * sample;
            }
            const rms = Math.sqrt(sumSquares / (buffer.length / 2)) / 32768;
            const now = Date.now();
            if (rms < TARGET_RMS && rms > MIN_RMS) { // Normalize audio if RMS is low
              const gain = Math.min(TARGET_RMS / rms, 2);
              for (let i = 0; i < buffer.length / 2; i++) {
                let sample = buffer.readInt16LE(i * 2);
                sample = Math.round(sample * gain);
                sample = Math.max(-32768, Math.min(32767, sample));
                buffer.writeInt16LE(sample, i * 2);
              }
              if (!rmsLogFrequency.has(channelId) || now - rmsLogFrequency.get(channelId) >= 2000) {
                logger.info(`Adjusted RMS from ${rms.toFixed(3)} to ~${TARGET_RMS} with gain ${gain.toFixed(2)} for channel ${channelId}`);
                rmsLogFrequency.set(channelId, now);
              }
            }

            // Обработка входящего аудио
            handleIncomingSpeech(channelId, buffer);
            if (!rmsLogFrequency.has(channelId) || now - rmsLogFrequency.get(channelId) >= 2000) {
              logger.info(`Обработка аудио для канала ${channelId} | Размер: ${(buffer.length / 1024).toFixed(2)} KB | RMS: ${rms.toFixed(3)}`);
              rmsLogFrequency.set(channelId, now);
            }
            audioBuffers.set(channelId, Buffer.alloc(0)); // Clear buffer after sending
          }
        }, BUFFER_INTERVAL_MS);
      }
    }
  });

  rtpReceiver.on('error', (err) => {
    logger.error(`RTP Receiver error: ${err.message}`);
    logger.error(`RTP ошибка со стеком: ${err.stack}`);
  });

  try {
    logger.info(`Пытаемся привязать RTP приемник к ${BIND_URL}:${RTP_PORT}`);
    rtpReceiver.bind(RTP_PORT, BIND_URL); // Bind to local port
    logger.info(`RTP Receiver успешно привязан к ${BIND_URL}:${RTP_PORT}`);
    logger.info(`Настройка обработки RTP-сообщений для сокета на ${RTP_PORT} порту`);
  } catch (err) {
    logger.error(`Ошибка при привязке RTP приемника: ${err.message}`);
  }
}

// Convert a single μ-law sample to 16-bit PCM
function muLawToPcm16(muLaw) {
  muLaw = ~muLaw & 0xFF; // Invert bits and mask
  const sign = (muLaw & 0x80) ? -1 : 1; // Extract sign
  const exponent = (muLaw & 0x70) >> 4; // Extract exponent
  const mantissa = muLaw & 0x0F; // Extract mantissa
  let sample = (exponent === 0) ? (mantissa * 8 + 16) : (1 << (exponent + 3)) * (mantissa + 16) - 128; // Decode sample
  sample = sign * sample;
  return Math.max(-32768, Math.min(32767, sample)); // Clamp to 16-bit range
}

// Convert μ-law buffer to 24kHz PCM with interpolation
function muLawToPcm24kHz(muLawBuffer, channelId) {
  const pcm8kHz = Buffer.alloc(muLawBuffer.length * 2); // Buffer for 8kHz PCM
  let maxSampleBefore = 0; // Track max sample before clamping
  let maxSampleAfter = 0; // Track max sample after clamping

  // Convert μ-law to 8kHz PCM
  for (let i = 0; i < muLawBuffer.length; i++) {
    let sample = muLawToPcm16(muLawBuffer[i]);
    maxSampleBefore = Math.max(maxSampleBefore, Math.abs(sample));
    sample = Math.round(sample);
    sample = Math.max(-32768, Math.min(32767, sample));
    maxSampleAfter = Math.max(maxSampleAfter, Math.abs(sample));
    pcm8kHz.writeInt16LE(sample, i * 2);
  }

  // Upsample to 24kHz with linear interpolation
  const pcm24kHz = Buffer.alloc(muLawBuffer.length * 3 * 2);
  let sumSquares = 0;
  for (let i = 0; i < muLawBuffer.length; i++) {
    const sample = pcm8kHz.readInt16LE(i * 2);
    const prevSample = i > 0 ? pcm8kHz.readInt16LE((i - 1) * 2) : sample;
    const nextSample = i < muLawBuffer.length - 1 ? pcm8kHz.readInt16LE((i + 1) * 2) : sample;
    const interp1 = Math.round((prevSample * 0.5 + sample * 0.5)); // First interpolated sample
    const interp2 = Math.round((sample * 0.75 + nextSample * 0.25)); // Second interpolated sample
    pcm24kHz.writeInt16LE(prevSample, (i * 3) * 2);
    pcm24kHz.writeInt16LE(interp1, (i * 3 + 1) * 2);
    pcm24kHz.writeInt16LE(interp2, (i * 3 + 2) * 2);
    sumSquares += prevSample * prevSample + interp1 * interp1 + interp2 * interp2; // For RMS calculation
  }

  const rms = Math.sqrt(sumSquares / (muLawBuffer.length * 3)) / 32768; // Calculate RMS
  if (!audioToTTSMap.has(channelId)) audioToTTSMap.set(channelId, Buffer.alloc(0));
  audioToTTSMap.set(channelId, Buffer.concat([audioToTTSMap.get(channelId), pcm24kHz])); // Добавляем в буфер TTS

  const now = Date.now();
  if (!amplificationLogFrequency.has(channelId) || now - amplificationLogFrequency.get(channelId) >= 2000) {
    logger.info(`Audio processed for channel ${channelId} | RMS: ${rms.toFixed(3)} | Max sample before: ${maxSampleBefore}, after: ${maxSampleAfter}`);
    amplificationLogFrequency.set(channelId, now); // Update log frequency
  }

  return pcm24kHz;
}

// Save PCM data as a WAV file
function saveWavFile(pcmData, filename, sampleRate) {
  const bitsPerSample = 16; // 16-bit audio
  const channels = 1; // Mono
  const byteRate = sampleRate * channels * (bitsPerSample / 8);
  const blockAlign = channels * (bitsPerSample / 8);
  const dataSize = pcmData.length;
  const fileSize = 36 + dataSize;

  const buffer = Buffer.alloc(44 + dataSize); // WAV header + data
  buffer.write('RIFF', 0);
  buffer.writeUInt32LE(fileSize, 4);
  buffer.write('WAVE', 8);
  buffer.write('fmt ', 12);
  buffer.writeUInt32LE(16, 16); // Subchunk size
  buffer.writeUInt16LE(1, 20); // PCM format
  buffer.writeUInt16LE(channels, 22);
  buffer.writeUInt32LE(sampleRate, 24);
  buffer.writeUInt32LE(byteRate, 28);
  buffer.writeUInt16LE(blockAlign, 32);
  buffer.writeUInt16LE(bitsPerSample, 34);
  buffer.write('data', 36);
  buffer.writeUInt32LE(dataSize, 40);
  pcmData.copy(buffer, 44); // Copy PCM data

  fs.writeFileSync(filename, buffer);
  logger.info(`Saved audio as ${filename}`);
}

// Save raw μ-law data to a file
function saveRawFile(data, filename) {
  fs.writeFileSync(filename, data);
  logger.info(`Saved raw μ-law as ${filename}`);
}

// Convert 16-bit PCM sample to μ-law
function pcm16ToMuLaw(sample) {
  const MAX = 32767;
  const MU = 255;
  const BIAS = 33;

  sample = Math.max(-MAX, Math.min(MAX, sample)); // Clamp to 16-bit range
  const sign = sample < 0 ? 0x80 : 0;
  let absSample = Math.abs(sample);

  if (absSample < 50) return 0x7F; // Silence threshold
  absSample += BIAS;

  const normalized = absSample / MAX;
  const muLaw = Math.log(1 + MU * normalized) / Math.log(1 + MU); // μ-law compression
  const quantized = Math.round(muLaw * 128);
  const exponent = Math.min(Math.floor(quantized / 16), 7);
  const mantissa = Math.min((quantized - (exponent * 16)), 15) & 0x0F;

  return ~(sign | (exponent << 4) | mantissa) & 0xFF; // Invert bits
}

// Resample 24kHz PCM to 8kHz
function resamplePcm24kHzTo8kHz(pcm24kHz) {
  const inSampleRate = 24000;
  const outSampleRate = 8000;
  const inSamples = pcm24kHz.length / 2;
  const outSamples = Math.floor(inSamples * outSampleRate / inSampleRate);
  const pcm8kHz = Buffer.alloc(outSamples * 2);

  for (let i = 0; i < outSamples; i++) {
    const srcPos = i * inSampleRate / outSampleRate;
    const srcIndex = Math.floor(srcPos);
    const frac = srcPos - srcIndex;

    if (srcIndex + 1 < inSamples) {
      const sample1 = pcm24kHz.readInt16LE(srcIndex * 2);
      const sample2 = pcm24kHz.readInt16LE((srcIndex + 1) * 2);
      const interpSample = Math.round(sample1 + frac * (sample2 - sample1)); // Linear interpolation
      pcm8kHz.writeInt16LE(interpSample, i * 2);
    } else if (srcIndex < inSamples) {
      pcm8kHz.writeInt16LE(pcm24kHz.readInt16LE(srcIndex * 2), i * 2);
    }
  }
  return pcm8kHz;
}

// Convert PCM buffer to μ-law, optionally resampling from 24kHz to 8kHz
function pcmToMuLaw(pcmBuffer, resample = false) {
  // Особая обработка для ElevenLabs PCM 16кГц -> PCM 8кГц -> μ-law
  if (resample && pcmBuffer.length > 0) {
    // Для ElevenLabs мы получаем 16-битный PCM с частотой 16кГц
    // Нам нужно преобразовать его в 8-битный μ-law с частотой 8кГц
    
    // Создаем буфер для μ-law (размер будет вдвое меньше из-за децимации и вдвое меньше из-за 16->8 бит)
    const muLawBuffer = Buffer.alloc(pcmBuffer.length / 4);
    
    // Логирование размеров буферов и их отношения
    logger.debug(`PCM буфер: ${pcmBuffer.length} байт, μ-law буфер: ${muLawBuffer.length} байт, отношение: ${pcmBuffer.length/muLawBuffer.length}`); 
    
    // Децимация (берем каждый второй сэмпл для преобразования 16кГц -> 8кГц)
    for (let i = 0, k = 0; i < pcmBuffer.length; i += 4, k++) {
      if (i + 1 < pcmBuffer.length) {
        // Читаем 16-битный сэмпл (2 байта)
        const sample = pcmBuffer.readInt16LE(i);
        
        // Преобразуем в μ-law с усилением (для лучшей громкости)
        const amplifiedSample = Math.max(-32767, Math.min(32767, Math.floor(sample * 2.5)));
        muLawBuffer[k] = pcm16ToMuLaw(amplifiedSample);
      }
    }
    
    return muLawBuffer;
  } else {
    // Оригинальная реализация для других случаев
    const input = pcmBuffer;
    const muLawBuffer = Buffer.alloc(input.length / 2);
    const chunkSize = 1024;
    
    for (let i = 0; i < input.length / 2; i += chunkSize) {
      const end = Math.min(i + chunkSize, input.length / 2);
      for (let j = i; j < end; j++) {
        let sample = input.readInt16LE(j * 2);
        sample = Math.max(-32767, Math.min(32767, Math.floor(sample * 1.2))); // Усиливаем звук
        muLawBuffer[j] = pcm16ToMuLaw(sample);
      }
    }
    
    return muLawBuffer;
  }
}

// Build RTP header for a packet
function buildRTPHeader(seq, timestamp, ssrc) {
  const header = Buffer.alloc(12);
  header[0] = 0x80; // Version 2, no padding, no extension
  header[1] = 0x00; // Payload type (0 for μ-law)
  header.writeUInt16BE(seq, 2); // Sequence number
  header.writeUInt32BE(timestamp, 4); // Timestamp
  header.writeUInt32BE(ssrc, 8); // Synchronization source
  return header;
}

// Async queue for sending RTP packets
const rtpQueue = async.queue((task, callback) => {
  rtpSender.send(task.packet, task.port, task.address, callback);
}, RTP_QUEUE_CONCURRENCY);

// Send an RTP packet with μ-law data
async function sendAudioPacket(muLawData, port, address, seq, timestamp, ssrc) {
  const startTime = process.hrtime.bigint();
  const header = buildRTPHeader(seq, timestamp, ssrc);
  const rtpPacket = Buffer.concat([header, muLawData]);
  await new Promise((resolve, reject) => {
    rtpQueue.push({ packet: rtpPacket, port, address }, (err) => {
      const elapsedMs = Number(process.hrtime.bigint() - startTime) / 1e6;
      if (ENABLE_RTP_LOGGING && seq % LOG_RTP_EVERY_N_PACKETS === 0) {
        logger.info(`Sent packet seq=${seq}, timestamp=${timestamp}, elapsed=${elapsedMs.toFixed(2)}ms`);
      }
      if (err) {
        logger.error(`Error sending RTP packet: ${err.message}`);
        reject(err);
      } else {
        resolve();
      }
    });
  });
}

// Stream audio to Asterisk via RTP
const MAX_BUFFER_SIZE = 1024 * 1024; // Max buffer size (1MB)
async function streamAudio(channelId, rtpSource, initialBuffer = Buffer.alloc(0)) {
  const samplesPerPacket = 80; // 10 ms at 8000 Hz
  const packetIntervalNs = BigInt(10 * 1e6); // 10 ms in nanoseconds
  const { address, port } = rtpSource;

  logger.info(`Initializing RTP stream to ${address}:${port} for channel ${channelId}`);

  let rtpSequence = Math.floor(Math.random() * 65535); // Random initial sequence
  let rtpTimestamp = 0; // Initial timestamp
  const rtpSSRC = Math.floor(Math.random() * 4294967295); // Random SSRC
  let streamStartTime = process.hrtime.bigint();
  let isStreaming = true;
  let totalBytesSent = 0;
  let totalPacketsSent = 0;
  let stopRequested = false;
  let lastBufferSize = 0; // Previous buffer size
  let wasSending = false; // Track if we were sending data

  let muLawBuffer = Buffer.alloc(0); // Buffer for μ-law data
  let offset = 0; // Offset in buffer

  if (!rtpSentStats.has(channelId)) {
    rtpSentStats.set(channelId, { packets: 0, bytes: 0, startTime: null }); // Initialize stats
  }

  // Send a batch of RTP packets
  const sendPackets = async (data, packetCount, isSilence = false) => {
    let blockStartTime = process.hrtime.bigint();
    let nextPacketTime = blockStartTime;

    for (let i = 0; i < packetCount && !stopRequested; i++) {
      const bytesToSend = Math.min(samplesPerPacket, data.length - (i * samplesPerPacket));
      const packetData = data.slice(i * samplesPerPacket, i * samplesPerPacket + bytesToSend);
      const packetDataPadded = bytesToSend < samplesPerPacket ? Buffer.concat([packetData, Buffer.alloc(samplesPerPacket - bytesToSend, 0x7F)]) : packetData;

      await sendAudioPacket(packetDataPadded, port, address, rtpSequence, rtpTimestamp, rtpSSRC);
      if (i === 0 && !streamStartTime) streamStartTime = process.hrtime.bigint();
      rtpSequence = (rtpSequence + 1) % 65536;
      rtpTimestamp += 80;
      totalBytesSent += packetDataPadded.length;
      totalPacketsSent += 1;

      const stats = rtpSentStats.get(channelId);
      stats.packets += 1;
      stats.bytes += packetDataPadded.length;
      if (!stats.startTime) stats.startTime = Date.now();

      nextPacketTime += packetIntervalNs;
      const now = process.hrtime.bigint();
      if (now < nextPacketTime) {
        const delayMs = Number(nextPacketTime - now) / 1e6;
        await new Promise(resolve => setTimeout(resolve, delayMs)); // Maintain timing
      }
    }
  };

  const silencePacket = Buffer.alloc(samplesPerPacket, 0x7F); // Silence packet
  await sendPackets(silencePacket, 10, true); // Send initial silence
  logger.info(`RTP stream fully initialized for channel ${channelId}`);

  // Process PCM chunks into μ-law
  const processFallback = async (pcmChunk) => {
    const muLawData = pcmToMuLaw(pcmChunk, true);
    muLawBuffer = Buffer.concat([muLawBuffer, muLawData]);
    if (muLawBuffer.length > MAX_BUFFER_SIZE) {
      muLawBuffer = muLawBuffer.slice(muLawBuffer.length - MAX_BUFFER_SIZE); // Trim buffer
    }
  };

  // Main streaming loop
  const streamLoop = async () => {
    while (isStreaming && !stopRequested) {
      if (!sipMap.has(channelId)) {
        logger.info(`Channel ${channelId} no longer active, stopping RTP stream`);
        break;
      }
      const currentBufferSize = muLawBuffer.length - offset;
      if (currentBufferSize >= samplesPerPacket) {
        const packetCount = Math.floor(currentBufferSize / samplesPerPacket);
        await sendPackets(muLawBuffer.slice(offset, offset + packetCount * samplesPerPacket), packetCount);
        offset += packetCount * samplesPerPacket;
        if (muLawBuffer.length - offset > MAX_BUFFER_SIZE / 2) {
          muLawBuffer = muLawBuffer.slice(offset);
          offset = 0; // Reset offset
        }
        wasSending = true;
      } else if (wasSending && currentBufferSize < samplesPerPacket) {
        logger.info(`RTP buffer to Asterisk fully sent for channel ${channelId} | Remaining: ${currentBufferSize} bytes`);
        wasSending = false;
      }
      lastBufferSize = currentBufferSize;
      await new Promise(resolve => setImmediate(resolve)); // Yield control
    }

    const totalDuration = Number(process.hrtime.bigint() - streamStartTime) / 1e9;
    logger.info(`Finished RTP stream for channel ${channelId} | Total duration: ${totalDuration.toFixed(2)}s | Total bytes sent: ${totalBytesSent} | Total packets: ${totalPacketsSent}`);
    rtpSentStats.set(channelId, { packets: 0, bytes: 0, startTime: null }); // Reset stats
  };

  streamLoop();

  // Stop the stream
  const stop = async () => {
    isStreaming = false;
    stopRequested = true;
    muLawBuffer = Buffer.alloc(0);
    offset = 0;
    logger.info(`RTP stream stopped for channel ${channelId}`);
  };

  return {
    stop,
    write: processFallback, // Method to write PCM data
    muLawBuffer,
    offset
  };
}

// Эта функция была удалена, так как мы перешли на ElevenLabs вместо OpenAI

// Функция для преобразования текста в речь с помощью ElevenLabs API
async function streamTextToSpeech(channelId, text) {
  logger.info(`Запрос преобразования текста в речь для канала ${channelId} | Текст: "${text}"`);
  
  const channelData = sipMap.get(channelId);
  if (!channelData) {
    logger.error(`Не найдены данные канала ${channelId} в sipMap`);
    return;
  }
  
  if (!channelData.rtpSource) {
    logger.error(`Отсутствует источник RTP для канала ${channelId}`);
    return;
  }
  
  if (!channelData.streamHandler) {
    logger.info(`Инициализация StreamHandler для канала ${channelId}`);
    try {
      channelData.streamHandler = await streamAudio(channelId, channelData.rtpSource);
      logger.info(`StreamHandler успешно инициализирован для канала ${channelId}`);
    } catch (err) {
      logger.error(`Ошибка инициализации StreamHandler для канала ${channelId}: ${err.message}`);
      return;
    }
  }
  
  try {
    // Формируем URL для запроса к ElevenLabs API
    const url = `${ELEVENLABS_API_URL}/text-to-speech/${ELEVENLABS_VOICE_ID}/stream`;
    
    // Упрощаем параметры запроса до минимально необходимых
    const requestData = {
      text: text,
      voice_settings: {
        stability: 0.5,
        similarity_boost: 0.75
      }
    };
    
    // Добавляем модель, только если она указана
    if (ELEVENLABS_MODEL_ID) {
      requestData.model_id = ELEVENLABS_MODEL_ID;
    }
    
    // Добавляем выходной формат, используем стандартный PCM
    requestData.output_format = 'pcm_16000';
    logger.info(`Используем формат PCM 16kHz для совместимости с Asterisk`);

    // Логируем параметры запроса
    logger.info(`Параметры запроса к ElevenLabs: ${JSON.stringify(requestData)}`);

    
    // Заголовки запроса
    const headers = {
      'xi-api-key': ELEVENLABS_API_KEY,
      'Content-Type': 'application/json',
      'Accept': 'audio/*'
    };
    
    logger.info(`Отправка запроса к ElevenLabs API для канала ${channelId}`);
    logger.info(`Запрос к URL: ${url}`);
    
    let response;
    try {
      // Выполняем запрос с потоковой обработкой ответа
      response = await axios({
        method: 'post',
        url: url,
        data: requestData,
        headers: headers,
        responseType: 'stream',
        validateStatus: false // Позволяет получить более подробную информацию об ошибке
      });
      
      // Проверяем статус ответа
      if (response.status !== 200) {
        // Собираем тело ответа для получения деталей ошибки
        let errorResponseBody = '';
        response.data.on('data', (chunk) => {
          errorResponseBody += chunk.toString();
        });

        response.data.on('end', () => {
          logger.error(`Ошибка ElevenLabs API (${response.status}): ${errorResponseBody}`);
        });

        throw new Error(`ElevenLabs API вернул API статус: ${response.status}`);
      }
    } catch (err) {
      // Детальное логирование ошибки
      logger.error(`Ошибка при запросе к ElevenLabs API для канала ${channelId}: ${err.message}`);

      // Используем заглушку - отправляем тишину вместо аудио
      logger.info(`Отправка тишины вместо аудио для канала ${channelId}`);
      if (channelData.streamHandler) {
        // Создаём пустой буфер шума
        const silenceBuffer = Buffer.alloc(8000); // 0.5 секунды тишины при 16kHz
        channelData.streamHandler.write(silenceBuffer);
      }
      
      return;
    }
    
    logger.info(`Получен ответ от ElevenLabs API для канала ${channelId}, начинаем обработку аудио потока`);
    
    // Обработка потока аудио
    const stream = response.data;
    let totalBytes = 0;
    let startTime = Date.now();
    
    // Создаем буфер для накопления аудио данных
    const chunks = [];
    
    stream.on('data', (chunk) => {
      totalBytes += chunk.length;
      
      // Сохраняем фрагмент в массив
      chunks.push(chunk);
      
      // Отправляем каждый фрагмент для минимизации задержки
      if (channelData.streamHandler && chunk.length > 0) {
        try {
          // Для PCM формата, отправляем напрямую
          if (ELEVENLABS_OUTPUT_FORMAT.startsWith('pcm_')) {
            // Преобразовываем 16kHz PCM в 8kHz для Asterisk если нужно
            if (ELEVENLABS_OUTPUT_FORMAT === 'pcm_16000') {
              // Корректное преобразование из 16-битного PCM 16кГц в 8-битный μ-law 8кГц
              
              // Создаем буфер для PCM данных
              try {
                // Более детальное логирование для отладки
                logger.debug(`Получен фрагмент PCM от ElevenLabs размером ${chunk.length} байт, 16kHz PCM`); 
                
                // Копируем в новый буфер
                const pcmData = Buffer.alloc(chunk.length);
                chunk.copy(pcmData);
                
                // Преобразуем 16kHz PCM в 8kHz μ-law
                const muLawData = pcmToMuLaw(pcmData, true);
                
                // Логируем размер на выходе
                logger.debug(`Преобразовано в μ-law, размер буфера: ${muLawData.length} байт`);
                
                // Отправляем данные в поток
                if (channelData.streamHandler) {
                  // Отправляем данные в RTP поток
                  const bytesSent = channelData.streamHandler.write(muLawData);
                  
                  if (bytesSent) {
                    logger.info(`Отправлено ${bytesSent} байт PCM/μ-law в RTP стрим`);
                  } else {
                    logger.warn(`Не удалось отправить данные в поток`);
                  }
                } else {
                  logger.error(`streamHandler не определен для канала ${channelId}`);
                }
              } catch (err) {
                logger.error(`Ошибка при преобразовании PCM в μ-law: ${err.message}`);
              }
            } else {
              // Отправляем как есть
              channelData.streamHandler.write(chunk);
              logger.debug(`Отправлен фрагмент PCM высотой ${chunk.length} байт в RTP стрим`);
            }
          } else {
            // Для других форматов (например, MP3) потребуется дополнительная конвертация
            logger.warn(`Формат ${ELEVENLABS_OUTPUT_FORMAT} не поддерживается напрямую, требуется конвертация`);
          }
        } catch (err) {
          logger.error(`Ошибка при обработке аудиофрагмента: ${err.message}`);
        }
      }
    });
    
    stream.on('end', () => {
      const duration = ((Date.now() - startTime) / 1000).toFixed(2);
      logger.info(`Потоковая передача аудио от ElevenLabs для канала ${channelId} завершена | Длительность: ${duration}с | Размер: ${(totalBytes / 1024).toFixed(2)} КБ`);
    });
    
    stream.on('error', (err) => {
      logger.error(`Ошибка при получении аудио потока от ElevenLabs для канала ${channelId}: ${err.message}`);
    });
    
    return true;
  } catch (err) {
    logger.error(`Ошибка при запросе к ElevenLabs API для канала ${channelId}: ${err.message}`);
    return false;
  }
}

// Функция для инициализации обработки голоса с помощью ElevenLabs
async function initializeElevenLabsTTS(channelId) {
  logger.info(`Инициализация обработки TTS ElevenLabs для канала ${channelId}`);
  
  const channelData = sipMap.get(channelId);
  if (!channelData) {
    logger.error(`Критическая ошибка: Не найдены данные канала ${channelId} в sipMap`);
    return;
  }
  
  // Обновляем функции в channelData
  channelData.getPlaybackComplete = () => false; // Значение по умолчанию
  channelData.stopStream = async () => {
    if (channelData.streamHandler) {
      await channelData.streamHandler.stop();
      channelData.streamHandler = null;
    }
  };
  
  // Отправляем приветственное сообщение
  const welcomeMessage = "Здравствуйте! Я голосовой помощник на базе ElevenLabs. Чем я могу вам помочь сегодня?";
  
  // Функция для ожидания установки rtpSource
  const waitForRtpSource = async (maxAttempts = 10, delay = 1000) => {
    for (let attempt = 0; attempt < maxAttempts; attempt++) {
      // Проверяем наличие rtpSource в канале
      const currentData = sipMap.get(channelId);
      if (currentData && currentData.rtpSource) {
        logger.info(`RTP источник найден для канала ${channelId} после ${attempt + 1} попыток`);
        return true;
      }
      
      // Ждем перед следующей попыткой
      logger.info(`Ожидание RTP источника для канала ${channelId}, попытка ${attempt + 1}/${maxAttempts}`);
      await new Promise(resolve => setTimeout(resolve, delay));
    }
    
    logger.error(`Не удалось дождаться RTP источника после ${maxAttempts} попыток для канала ${channelId}`);
    return false;
  };
  
  // Запускаем процесс ожидания и отправки приветствия
  setTimeout(async () => {
    try {
      // Ждем, пока установится rtpSource
      const rtpReady = await waitForRtpSource();
      if (!rtpReady) {
        logger.error(`Невозможно отправить приветственное сообщение: RTP источник недоступен`);
        return;
      }
      
      // Пытаемся инициализировать StreamHandler если ещё не инициализирован
      const currentChannelData = sipMap.get(channelId);
      if (!currentChannelData.streamHandler && currentChannelData.rtpSource) {
        currentChannelData.streamHandler = await streamAudio(channelId, currentChannelData.rtpSource);
        logger.info(`StreamHandler успешно инициализирован для канала ${channelId}`);
      }
      
      // Отправляем приветственное сообщение
      await streamTextToSpeech(channelId, welcomeMessage);
      logger.info(`Приветственное сообщение отправлено для канала ${channelId}`);
    } catch (err) {
      logger.error(`Ошибка при инициализации TTS для канала ${channelId}: ${err.message}`);
    }
  }, 1000);
}

// Функция для обработки входящей речи и отправки ответа
let speechDetected = new Map(); // Хранит информацию о состоянии распознавания речи для каждого канала

async function handleIncomingSpeech(channelId, buffer) {
  // Для простоты используем определение речи на основе громкости (RMS)
  // В реальном приложении здесь должен быть более сложный алгоритм VAD или ASR
  const channelData = sipMap.get(channelId);
  if (!channelData) return;
  
  let sumSquares = 0;
  for (let i = 0; i < buffer.length / 2; i++) {
    const sample = buffer.readInt16LE(i * 2);
    sumSquares += sample * sample;
  }
  const rms = Math.sqrt(sumSquares / (buffer.length / 2)) / 32768;
  
  // Простой алгоритм обнаружения речи
  if (rms > 0.02) { // Порог обнаружения речи
    if (!speechDetected.has(channelId)) {
      logger.info(`Обнаружена речь для канала ${channelId}, RMS: ${rms.toFixed(3)}`);
      speechDetected.set(channelId, {
        startTime: Date.now(),
        endTime: Date.now(),
        buffers: []
      });
    } else {
      const speechData = speechDetected.get(channelId);
      speechData.endTime = Date.now();
      speechData.buffers.push(buffer);
      speechDetected.set(channelId, speechData);
    }
  } else if (speechDetected.has(channelId)) {
    const speechData = speechDetected.get(channelId);
    const now = Date.now();
    
    // Если тишина длится более 1 секунды после обнаруженной речи,
    // считаем, что фраза закончена
    if (now - speechData.endTime > 1000) {
      const duration = (speechData.endTime - speechData.startTime) / 1000;
      logger.info(`Речь завершена для канала ${channelId}, длительность: ${duration.toFixed(2)}с`);
      
      // Здесь должен быть код для распознавания речи
      // Но поскольку нет интеграции с ASR, просто отправляем предопределенный ответ
      const response = "Здравствуйте! Я голосовой помощник на базе ElevenLabs. К сожалению, я не могу распознать вашу речь, но я могу отвечать на команды. В данный момент мы заменили OpenAI на ElevenLabs для генерации речи.";
      
      // Используем ElevenLabs для ответа
      await streamTextToSpeech(channelId, response);
      
      // Сбрасываем состояние распознавания
      speechDetected.delete(channelId);
    }
  }
}

// Main async function to initialize ARI and handle events
(async () => {
  try {
    // Инициализация глобальных переменных
    logger.info(`Запуск приложения с переменными окружения: BIND_URL=${BIND_URL}, RTP_PORT=${RTP_PORT}`);
    logger.info(`Статус глобального rtpReceiver: ${rtpReceiver ? 'инициализирован' : 'не инициализирован'}`);
    
    ariClient = await ari.connect(ARI_URL, ARI_USER, ARI_PASS); // Connect to ARI
    logger.info(`Connected to ARI at ${ARI_URL}`);
    await ariClient.start(ARI_APP); // Start Stasis app
    logger.info(`ARI application "${ARI_APP}" started`);

    logger.info(`Вызываем функцию startRTPReceiver() для начала приема RTP пакетов`);
    startRTPReceiver(); // Start RTP receiver
    logger.info(`Функция startRTPReceiver() выполнена`);

    // Handle new channel entering Stasis
    ariClient.on('StasisStart', async (evt, channel) => {
      logger.info(`StasisStart event received for channel ${channel.id}, name: ${channel.name}`);
      
      // Проверяем, является ли это исходящим вызовом ElevenLabs
      const args = evt.args || [];
      if (args.includes('outbound_elevenlabs')) {
        logger.info(`Обработка исходящего вызова ElevenLabs: ${channel.id}`);
        
        // Инициализируем обработку состояния исходящего звонка
        if (!sipMap.has(channel.id)) {
          sipMap.set(channel.id, {
            isOutbound: true,
            elevenlabsMessage: channel.getVariable('ELEVENLABS_MESSAGE') || 'Привет, это тестовое сообщение от ElevenLabs!',
            answered: false
          });
        }
        
        // Слушаем событие ChannelStateChange для обработки ответа на звонок
        channel.on('ChannelStateChange', async (event) => {
          if (event.channel.state === 'Up' && sipMap.has(channel.id)) {
            const channelData = sipMap.get(channel.id);
            if (channelData.isOutbound && !channelData.answered) {
              logger.info(`Абонент ответил на звонок: ${channel.id}`);
              channelData.answered = true;
              sipMap.set(channel.id, channelData);
              
              // Проигрываем сообщение ElevenLabs
              await playElevenLabsMessage(channel.id);
            }
          }
        });
        
        return; // Завершаем обработку события для исходящих вызовов
      }
      
      if (channel.name && channel.name.startsWith('UnicastRTP')) { // ExternalMedia channel
        logger.info(`ExternalMedia channel started: ${channel.id}`);
        let mapping = extMap.get(channel.id);
        if (!mapping) {
          await new Promise(r => setTimeout(r, 500)); // Wait for mapping
          mapping = extMap.get(channel.id);
        }
        if (mapping) {
          await addExtToBridge(ariClient, channel, mapping.bridgeId);
          const channelData = sipMap.get(mapping.channelId);
          if (channelData && !channelData.rtpSource) {
            // Извлекаем информацию из имени канала UnicastRTP
            const rtpMatch = channel.name.match(/UnicastRTP\/([\d\.]+):(\d+)/); // Получаем IP и порт из имени
            
            if (rtpMatch) {
              // Устанавливаем rtpSource на основе имени канала
              channelData.rtpSource = {
                address: rtpMatch[1],
                port: parseInt(rtpMatch[2], 10)
              };
              logger.info(`RTP Source extracted from channel name for ${mapping.channelId}: ${channelData.rtpSource.address}:${channelData.rtpSource.port}`);
            } else {
              // Запасной вариант - используем настройки по умолчанию
              const localAddress = BIND_URL === '0.0.0.0' ? '127.0.0.1' : BIND_URL;
              channelData.rtpSource = {
                address: localAddress,
                port: RTP_PORT
              };
              logger.info(`RTP Source set to default for ${mapping.channelId}: ${channelData.rtpSource.address}:${channelData.rtpSource.port}`);
            }
            
            // Инициализируем обработчик потока теперь, когда у нас есть источник
            // Начинаем обработку ElevenLabs TTS если еще не начали
            (async () => {
              try {
                // Создаем streamHandler для голосовых ответов
                if (!channelData.streamHandler) {
                  channelData.streamHandler = await streamAudio(mapping.channelId, channelData.rtpSource);
                  logger.info(`StreamHandler создан для канала ${mapping.channelId}`);
                }
              } catch (err) {
                logger.error(`Ошибка при инициализации StreamHandler: ${err.message}`);
              }
            })();
            
            // Также будем отслеживать фактические RTP пакеты для логирования
            rtpReceiver.once('message', (msg, rinfo) => {
              logger.info(`First RTP packet received for channel ${mapping.channelId} from ${rinfo.address}:${rinfo.port}`);
            });
          }
        }
        return;
      }
      logger.info(`SIP channel started: ${channel.id}`);
      try {
        const bridge = await ariClient.bridges.create({ type: 'mixing,proxy_media' }); // Create mixing bridge
        await bridge.addChannel({ channel: channel.id });

        await channel.answer(); // Answer the call
        logger.info(`Channel ${channel.id} answered`);

        // Устанавливаем канал ExternalMedia
        const extParams = {
          app: ARI_APP,
          external_host: `${BIND_URL}:${RTP_PORT}`, // Используем формат host:port (0.0.0.0:12000)
          format: 'ulaw',
          transport: 'udp',
          encapsulation: 'rtp',
          connection_type: 'client',
          direction: 'both'
        };
        const extChannel = await ariClient.channels.externalMedia(extParams);
        extMap.set(extChannel.id, { bridgeId: bridge.id, channelId: channel.id });
        logger.info(`ExternalMedia channel ${extChannel.id} created and mapped to bridge ${bridge.id}`);

        // Создаем запись в sipMap для данного канала
        sipMap.set(channel.id, {
          bridge: bridge,
          channelId: channel.id,
          sendTimeout: null,
          getPlaybackComplete: () => false, // Значение по умолчанию
          stopStream: async () => {}, // Значение по умолчанию
          rtpSource: null, // Будет установлено когда UnicastRTP начнется
          streamHandler: null // Будет установлено функцией initializeStreamHandler
        });

        // Инициализируем обработку аудио с помощью ElevenLabs
        initializeElevenLabsTTS(channel.id);
      } catch (e) {
        logger.error(`Error in SIP channel ${channel.id}: ${e.message}`);
      }
    });

    // Handle channel leaving Stasis (call end)
    ariClient.on('StasisEnd', async (evt, channel) => {
      if (channel.name && channel.name.startsWith('UnicastRTP')) {
        extMap.delete(channel.id);
        logger.info(`ExternalMedia channel ${channel.id} removed from map`);
      } else {
        const channelData = sipMap.get(channel.id);
        if (channelData) {
          try {
            sipMap.delete(channel.id);
            logger.info(`Channel ${channel.id} removed from sipMap at start of StasisEnd`);

            if (channelData.sendTimeout) {
              clearInterval(channelData.sendTimeout);
              channelData.sendTimeout = null;
              logger.info(`Send timeout cleared for channel ${channel.id}`);
            }

            if (channelData.stopStream) {
              await channelData.stopStream();
              logger.info(`StreamHandler stopped for channel ${channel.id} in StasisEnd`);
            }

            if (!channelData.getPlaybackComplete()) {
              logger.info(`Channel ${channel.id} hung up, checking playback status before cleanup`);
              await new Promise(resolve => setTimeout(resolve, 100)); // Brief delay
            }

            // Для ElevenLabs не нужно закрывать WebSocket

            await channelData.bridge.destroy();
            logger.info(`Bridge ${channelData.bridge.id} destroyed`);
          } catch (e) {
            logger.error(`Error during cleanup for channel ${channel.id}: ${e.message}`);
          }
        }
        logger.info(`Channel ended: ${channel.id}`);

        // Сохранение аудиофайлов при использовании ElevenLabs не реализовано
      }
    });

    ariClient.on('error', (err) => logger.error(`ARI client error: ${err.message}`));
    ariClient.on('close', () => logger.info('ARI WebSocket connection closed'));
    
    // Экспортируем функции для инициации звонков через внешний API
    module.exports = {
      initiateElevenLabsCall,
      playElevenLabsMessage
    };
  } catch (err) {
    logger.error(`ARI connection error: ${err.message}`);
    process.exit(1); // Exit on connection failure
  }
})();

// Handle uncaught exceptions
process.on('uncaughtException', (err) => {
  logger.error(`Uncaught Exception: ${err.message}`);
  cleanup();
  process.exit(1);
});

// Handle SIGINT (Ctrl+C)
process.on('SIGINT', () => {
  logger.info('Received SIGINT, cleaning up...');
  cleanup();
  process.exit(0);
});

// Инициирует звонок от ElevenLabs к указанному абоненту
async function initiateElevenLabsCall(destination, message, options = {}) {
  try {
    logger.info(`Инициирование звонка к абоненту: ${destination}`);
    
    // Параметры по умолчанию или пользовательские
    const callerId = options.callerId || DEFAULT_CALLER_ID;
    const context = options.context || DEFAULT_CONTEXT;
    const extension = options.extension || destination;
    const priority = options.priority || DEFAULT_PRIORITY;
    const variables = options.variables || {};
    
    // Создаем исходящий канал через ARI
    const channel = await ariClient.channels.originate({
      endpoint: `PJSIP/${destination}`,
      callerId: callerId,
      app: ARI_APP,
      appArgs: 'outbound_elevenlabs',
      context: context,
      extension: extension,
      priority: priority,
      variables: {
        ELEVENLABS_MESSAGE: message,
        ...variables
      }
    });
    
    logger.info(`Звонок инициирован, ID канала: ${channel.id}`);
    
    // Сохраняем сообщение для проигрывания после ответа
    sipMap.set(channel.id, {
      ...sipMap.get(channel.id) || {},
      elevenlabsMessage: message,
      isOutbound: true
    });
    
    return {
      success: true,
      channelId: channel.id,
      message: `Звонок к абоненту ${destination} успешно инициирован`
    };
  } catch (error) {
    logger.error(`Ошибка инициирования звонка: ${error.message}`);
    return {
      success: false,
      error: error.message
    };
  }
}

// Запускает проигрывание сообщения ElevenLabs после ответа на звонок
async function playElevenLabsMessage(channelId) {
  try {
    const channelData = sipMap.get(channelId);
    if (!channelData || !channelData.elevenlabsMessage) {
      throw new Error('Сообщение для проигрывания не найдено');
    }
    
    logger.info(`Проигрывание сообщения ElevenLabs для канала ${channelId}`);
    
    // Создаем bridge для исходящего звонка, если его нет
    if (!channelData.bridgeId) {
      const bridge = await ariClient.bridges.create({ type: 'mixing' });
      channelData.bridgeId = bridge.id;
      sipMap.set(channelId, channelData);
      
      // Добавляем канал в мост
      await ariClient.bridges.addChannel({
        bridgeId: bridge.id,
        channel: channelId
      });
    }
    
    // Инициализируем ElevenLabs и запускаем TTS
    await initializeElevenLabsTTS(channelId);
    await streamTextToSpeech(channelId, channelData.elevenlabsMessage);
    
    return {
      success: true,
      message: 'Сообщение успешно воспроизведено'
    };
  } catch (error) {
    logger.error(`Ошибка воспроизведения сообщения: ${error.message}`);
    return {
      success: false,
      error: error.message
    };
  }
}

// Cleanup function to close sockets and connections
function cleanup() {
  sipMap.forEach((data, channelId) => {
    if (data.sendTimeout) clearInterval(data.sendTimeout); // Clear send interval
    if (data.stopStream) data.stopStream(); // Stop RTP stream
  });
  rtpSender.close(); // Close RTP sender socket
  rtpReceiver.close(); // Close RTP receiver socket
}
