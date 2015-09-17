-- Frank Recker, 2015
module Main(main) where
import Control.Exception
import Control.Monad
import Crypto.Cipher.AES
import Crypto.PBKDF.ByteString
import Data.Bits
import Data.Word
import RandomMonad
import System.Environment
import System.IO
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.HMAC as HM

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  getArgs >>= \args -> case args of
    ["e",inp,out] -> encrypt_file count inp out
    ["d",inp,out] -> decrypt_file count inp out
    _ -> putStrLn "usage: crypt-file {e|d} <input-file> <output-file>"
  where
    count = 64 * 4096

-- High Level Functions
encrypt_file :: Int -> FilePath -> FilePath -> IO ()
encrypt_file count f g = do
  password <- read_pw
  (salt,iv) <- runRandomMonad $ random_salt_and_iv
  bracket (openBinaryFile f ReadMode) hClose $ \in_handle -> do
    plain <- BL.hGetContents in_handle
    let cipher = encrypt_bs password salt iv count plain
    bracket (openBinaryFile g WriteMode) hClose $ \out_handle -> do
      forM_ cipher $ \c -> do
        BL.hPut out_handle c

decrypt_file :: Int -> FilePath -> FilePath -> IO ()
decrypt_file count f g = do
  password <- read_pw
  bracket (openBinaryFile f ReadMode) hClose $ \in_handle -> do
    cipher <- BL.hGetContents in_handle
    let plain = decrypt_bs password count cipher
    bracket (openBinaryFile g WriteMode) hClose $ \out_handle -> do
      BL.hPut out_handle plain

encrypt_bs :: [Word8] -> [Word8] -> [Word8] -> Int -> BL.ByteString -> [BL.ByteString]
encrypt_bs password salt iv count plain
  | map length [salt,iv] == [32,16] = hmac_container
  where
    hmac_container = cipher_container ++ [BL.pack $ check20 hmac]
    hmac = my_hmac key2 $ concat $ map BL.unpack cipher_container
    cipher_container = map BL.pack [salt,iv,cipher]
    cipher = encrypt_aes_cbc key1 iv $ padding $ BL.unpack plain
    (key1,key2) = create_keys password salt count
    check20 as
       | length as==20 = as

decrypt_bs :: [Word8] -> Int -> BL.ByteString -> BL.ByteString
decrypt_bs password count hmac_container
  | hmac_soll /= hmac_ist = error "hmac is wrong"
  | otherwise = plain
  where
    plain = BL.pack $ unpadding $ decrypt_aes_cbc key1 iv $ BL.unpack cipher
    hmac_ist = my_hmac key2 $ BL.unpack cipher_container
    (key1,key2) = create_keys password salt count
    ([salt,iv],cipher) = my_take_many [32,16] cipher_container
    (cipher_container,hmac_soll) = take_from_the_end 20 hmac_container

create_keys :: [Word8] -> [Word8] -> Int -> ([Word8],[Word8])
create_keys password salt count =
  (key1,key2)
  where
    (key1,key2) = splitAt 32 pre_key
    pre_key = create_key password salt count 64

-- random salt und iv
random_salt_and_iv :: RandomMonad ([Word8],[Word8])
random_salt_and_iv = do
  salt <- random_bytes 32
  iv <- random_bytes 16
  return (salt,iv)

-- Low Level Function
my_take_many :: [Int] -> BL.ByteString -> ([[Word8]],BL.ByteString)
my_take_many (k:ks) xs =
  (y:ys,xs'')
  where
    (y,xs') = my_take k xs
    (ys,xs'') = my_take_many ks xs'
my_take_many [] xs = ([],xs)

my_take :: Int -> BL.ByteString -> ([Word8],BL.ByteString)
my_take k xs
  | length ys == k = (ys,zs)
  where
    ys = BL.unpack ys'
    (ys',zs) = BL.splitAt k' xs
    k' = fromIntegral k

take_from_the_end :: Int -> BL.ByteString -> (BL.ByteString,[Word8])
take_from_the_end k xs
  | n>=k' = (ys,BL.unpack zs)
  where
    (ys,zs) = BL.splitAt (n - k') xs
    n = BL.length xs
    k' = fromIntegral k

-- read the password from the keyboard
read_pw :: IO [Word8]
read_pw = do
  putStr "Password: "
  password <- BS.getLine
  return $ BS.unpack password

-- n random Bytes
random_bytes :: Int -> RandomMonad [Word8]
random_bytes n =
  forM [0..n-1] $ \i -> one_random_byte
  where
    one_random_byte :: RandomMonad Word8
    one_random_byte = getRandom

-- create a key
create_key :: [Word8] -> [Word8] -> Int -> Int -> [Word8]
create_key password salt count len =
  BS.unpack $ sha512PBKDF2 (BS.pack password) (BS.pack salt) count len

-- encrypt with AES-CBC
encrypt_aes_cbc :: [Word8] -> [Word8] -> [Word8] -> [Word8]
encrypt_aes_cbc key iv plain
  | length key == 32 && length iv == 16 = cipher
  where
    cipher = concat $ encrypt_cbc iv plain
    encrypt_cbc last_cipher_block [] = []
    encrypt_cbc last_cipher_block ys
      | length zs==16 = new_cipher_block:encrypt_cbc new_cipher_block zss
      where
        new_cipher_block = BS.unpack (encryptECB aes (BS.pack $ zipWith xor zs last_cipher_block))
        (zs,zss) = splitAt 16 ys
    aes = initAES (BS.pack key)

-- decrypt with AES-CBC
decrypt_aes_cbc :: [Word8] -> [Word8] -> [Word8] -> [Word8]
decrypt_aes_cbc key iv cipher
  | length key == 32 && length iv == 16 = plain
  where
    plain = concat $ decrypt_cbc iv cipher
    decrypt_cbc last_cipher_block [] = []
    decrypt_cbc last_cipher_block ys
      | length zs==16 = zipWith xor (BS.unpack $ decryptECB aes (BS.pack zs)) last_cipher_block:decrypt_cbc zs zss
      | otherwise = error "cipher-text has wrong length"
      where
        (zs,zss) = splitAt 16 ys
    aes = initAES (BS.pack key)

-- hmac with length 20 Bytes
my_hmac :: [Word8] -> [Word8] -> [Word8]
my_hmac key text
  | length key == 32 = HM.hmac_sha1 key text

-- Padding to 16 Bytes
padding :: [Word8] -> [Word8]
padding xs
  | n == 16 = ys ++ (padding zs)
  | n<16 = ys ++ (take (16-fromIntegral n) (1:repeat 0))
  where
    n = length ys
    (ys,zs) = splitAt 16 xs

unpadding :: [Word8] -> [Word8]
unpadding xs
  | n<16 = error "Padding-Error 1"
  | null zs = reverse $ tail_1 $ dropWhile (==0) $ reverse ys
  | otherwise = ys ++ (unpadding zs)
  where
    n = length ys
    (ys,zs) = splitAt 16 xs

tail_1 :: [Word8] -> [Word8]
tail_1 xs
  | x==1 = ys
  | otherwise = error "Padding-Error 2"
  where
    x = head xs
    ys = tail xs
