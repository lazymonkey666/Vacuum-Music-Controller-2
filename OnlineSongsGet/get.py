import os
import requests
import time
from pyncm import apis
from mutagen.mp3 import EasyMP3
from mutagen.id3 import ID3, APIC, USLT
import threading

class OnlineDownloader:
    def __init__(self, enable_api=True):
        # 初始化配置
        self.download_dir =  os.path.expanduser("~") + "\\AppData\\Roaming\\Vacuum\\Vacuum_Music_Player\\downloads\\songs"
        self.cover_dir =  os.path.expanduser("~") + "\\AppData\\Roaming\\Vacuum\\Vacuum_Music_Player\\downloads\\covers"
        self.max_size = 1024 * 1024 * 4096  # 4096MB
        self.headers = {
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/143.0.0.0 Safari/537.36 Edg/143.0.0.0",
            "Referer": "https://music.163.com/"
        }
        # 重试配置
        self.retry_config = {
            'max_retries': 3,
            'delay': 1
        }
        # 是否启用第三方API下载VIP歌曲
        self.enable_api = enable_api
        # 匿名登录
        apis.login.LoginViaAnonymousAccount()
        # 创建目录
        self._create_directories()

    def _create_directories(self):
        """创建下载目录"""
        for dir_path in [self.download_dir, self.cover_dir]:
            if not os.path.exists(dir_path):
                os.makedirs(dir_path)
                print(f"创建目录: {dir_path}")

    def _get_dir_size(self, path):
        """计算目录总大小"""
        total = 0
        for dirpath, dirnames, filenames in os.walk(path):
            for f in filenames:
                try:
                    total += os.path.getsize(os.path.join(dirpath, f))
                except OSError:
                    pass  # 忽略无法访问的文件
        return total

    def _sanitize_filename(self, filename):
        """清理文件名中的非法字符（增强版）"""
        invalid_chars = '/\\:*?"<>|'
        valid_chars = "-_.() %s%s,，：:" % (chr(10), chr(13))
        for c in invalid_chars:
            filename = filename.replace(c, '-')
        return ''.join(c for c in filename if c.isalnum() or c in valid_chars).strip()

    def _get_track_detail(self, track_id):
        """获取歌曲详情（带重试机制）"""
        for _ in range(self.retry_config['max_retries']):
            try:
                detail_res = apis.track.GetTrackDetail(track_id)
                if detail_res.get('code') != 200 or not detail_res.get('songs'):
                    time.sleep(self.retry_config['delay'])
                    continue
                return detail_res
            except Exception:
                time.sleep(self.retry_config['delay'])
        return None

    def _get_vip_track_audio(self, track_id):
        """获取VIP歌曲音频信息（包含重试机制）"""
        url = f"https://api.vkeys.cn/v2/music/netease?id={track_id}&quality=4"
        for _ in range(self.retry_config['max_retries']):
            try:
                response = requests.get(url, headers=self.headers, timeout=10)
                audio_res = response.json()
                if audio_res.get('code') != 200 or not audio_res.get('data'):
                    time.sleep(self.retry_config['delay'])
                    continue
                return audio_res
            except Exception as e:
                print(f"VIP接口请求失败，重试中...")
                print(e)
                time.sleep(self.retry_config['delay'])
        return False

    def _get_track_audio(self, track_id):
        """获取普通歌曲音频信息"""
        return apis.track.GetTrackAudio(track_id)

    def _process_track_tags(self, song_detail, track_id):
        """处理歌曲标签信息"""
        # 提取歌曲基本信息
        title = self._sanitize_filename(song_detail.get('name', ''))
        
        # 处理艺术家信息
        artists = []
        for ar in song_detail.get('ar', []):
            artist_name = ar.get('name', '')
            if artist_name:
                artists.append(artist_name)
        
        # 处理专辑信息
        album_info = song_detail.get('al', {})
        album_name = self._sanitize_filename(album_info.get('name', ''))
        
        return {
            'title': title,
            'artist': '/'.join(artists),
            'album': album_name,
            'artists': artists,
            'album_id': album_info.get('id'),
            'album_pic_url': album_info.get('picUrl', ''),
            'track_id': track_id,
            'duration': song_detail.get('dt', 0),  # 时长(毫秒)
            'publish_time': song_detail.get('publishTime', 0),
            'fee': song_detail.get('fee', 0)  # 是否VIP歌曲
        }

    def get_track_info(self, track_id, detail_res=None):
        """获取歌曲详细信息"""
        # 获取歌曲详情
        if not detail_res:
            detail_res = self._get_track_detail(track_id)
            if not detail_res:
                print(f"获取 {track_id} 歌曲详情失败!")
                return None

        # 检查是否为VIP歌曲
        songs = detail_res.get('songs', [])
        if not songs:
            print(f"歌曲 {track_id} 详情中无歌曲信息!")
            return None
        
        song_detail = songs[0]
        is_vip = song_detail.get('fee', 0) == 1
        
        # 判断是否为VIP歌曲并获取歌曲音频信息
        if is_vip and self.enable_api:
            print(f"{track_id} 为VIP歌曲, 使用落月API下载...")
            audio_res = self._get_vip_track_audio(track_id)
            if not audio_res:
                print(f"获取 {track_id} VIP音频信息失败!")
                return None
            try:
                audio_info = audio_res['data']
            except (TypeError, KeyError):
                print(f"解析 {track_id} VIP音频信息失败!")
                return None

        elif is_vip and not self.enable_api:
            print(f"{track_id} 为VIP歌曲, 跳过下载...")
            return None

        else:
            # 非VIP歌曲
            audio_res = self._get_track_audio(track_id)
            if audio_res.get('code') != 200 or not audio_res.get('data'):
                print(f"获取 {track_id} 普通音频信息失败!")
                return None
            audio_info = audio_res['data'][0]

        # 处理歌曲标签
        tags = self._process_track_tags(song_detail, track_id)

        # 处理专辑封面
        cover_url = song_detail.get('al', {}).get('picUrl', '')

        return {
            'id': track_id,
            'name': tags.get('title'),
            'artist': tags.get('artist'),
            'album': tags.get('album'),
            'url': audio_info.get('url', ''),
            'cover_url': cover_url,
            'tags': tags,
            'bitrate': audio_info.get('br', 320) if 'br' in audio_info else 320,
            'is_vip': is_vip,
            'artists': tags.get('artists', []),
            'duration': tags.get('duration', 0)
        }

    def download_cover(self, track_info):
        """下载专辑封面"""
        if not track_info or not track_info.get('cover_url'):
            return None

        try:
            # 使用歌曲ID或专辑名作为封面文件名
            cover_name = f"{track_info['id']}_{track_info['album']}.jpg"
            cover_name = self._sanitize_filename(cover_name)
            cover_path = os.path.join(self.cover_dir, cover_name)
            
            if os.path.exists(cover_path):
                return cover_path

            response = requests.get(track_info['cover_url'], headers=self.headers, timeout=10)
            response.raise_for_status()
            
            with open(cover_path, 'wb') as f:
                f.write(response.content)
            print(f"封面下载完成: {track_info['album']}")
            return cover_path
        except Exception as e:
            print(f"封面下载失败: {str(e)}")
            return None

    def download_audio(self, track_info):
        
        if f"{track_info['id']}_ {track_info['name']} - {track_info['artist']}.mp3" in os.listdir(self.download_dir):
            print(f"文件已存在，跳过下载: {track_info['id']}_ {track_info['name']} - {track_info['artist']}.mp3")
            return os.path.join(self.download_dir, f"{track_info['id']}_ {track_info['name']} - {track_info['artist']}.mp3"),True
        if not track_info or not track_info.get('url'):
            print("无有效音频URL")
            return None,False

        try:
            # 构建文件名：歌曲名 - 艺术家 [比特率kbps].mp3
            file_name = f"{track_info['id']}_ {track_info['name']} - {track_info['artist']}.mp3"
            file_name = self._sanitize_filename(file_name)
            file_path = os.path.join(self.download_dir, file_name)
            os.makedirs(os.path.dirname(file_path), exist_ok=True)
            
                
            # 检查文件是否已存在
            if os.path.exists(file_path):
                print(f"文件已存在，跳过下载: {file_name}")
                return file_path,False

            print(f"开始下载: {file_name}")
            response = requests.get(track_info['url'], headers=self.headers, stream=True, timeout=30)
            response.raise_for_status()
            
            total_size = int(response.headers.get('content-length', 0))
            downloaded = 0
            
            with open(file_path, 'wb') as f:
                for chunk in response.iter_content(chunk_size=8192):
                    if chunk:
                        f.write(chunk)
                        downloaded += len(chunk)
                        # 显示下载进度
                        if total_size > 0:
                            percent = (downloaded / total_size) * 100
                            print(f"\r下载进度: {percent:.1f}%", end="")
            
            print(f"\n歌曲下载完成: {file_name}")
            return file_path,False
        except Exception as e:
            print(f"歌曲下载失败: {str(e)}")
            return None,False

    def set_audio_tags(self, file_path, track_info, cover_path,lyrics):
        """设置音频文件标签"""
        try:
            # 设置基本标签
            audio = EasyMP3(file_path)
            audio['title'] = track_info['name']
            audio['artist'] = track_info['artist']
            audio['album'] = track_info['album']
            audio['tracknumber'] = str(track_info.get('id', ''))
            
            # 添加时长信息（转换为秒）
            duration = track_info.get('duration', 0)
            if duration > 0:
                audio['length'] = str(duration // 1000)
            
            audio.save()

            # 设置封面
            if cover_path and os.path.exists(cover_path):
                audio = ID3(file_path)
                with open(cover_path, 'rb') as f:
                    audio['APIC'] = APIC(
                        encoding=3,
                        mime='image/jpeg',
                        type=3,
                        desc='Cover',
                        data=f.read()
                    )
                if lyrics:
                    audio['USLT'] = USLT(encoding=3, text=lyrics)
                audio.save()
            print("标签设置完成")
        except Exception as e:
            print(f"标签设置失败: {str(e)}")
    def get_storage_size(self):#自动删除最老的部分
        if self._get_dir_size(self.download_dir) >= self.max_size:
            all_music = []
            for file in os.listdir(self.download_dir):  
                file_path = os.path.join(self.download_dir, file)
                all_music.append((os.path.getctime(file_path), file_path))
            all_music.sort()  # 按创建时间排序，最老的在前
            while self._get_dir_size(self.download_dir) >= self.max_size and all_music:
                oldest_time, oldest_path = all_music.pop(0)
                try:
                    os.remove(oldest_path)
                    print(f"删除最老文件: {os.path.basename(oldest_path)}")
                except OSError as e:
                    print(f"删除文件失败: {e}")
        return True
    def remove_cover(self,file):
        os.remove(file)
    def download(self, track_id):
        """下载主流程"""
        print(f"开始处理歌曲ID: {track_id}")
        
        # 获取歌曲信息
        track_info = self.get_track_info(track_id)
        if not track_info:
            print(f"歌曲 {track_id} 信息获取失败，跳过下载")
            return None
        
        print(f"获取到歌曲信息: {track_info['name']} - {track_info['artist']}")
        audio_path,flag = self.download_audio(track_info)
        if flag:
            return audio_path,""
        # 下载封面
        cover_path = self.download_cover(track_info)
        
        # 下载音频
        
        if not audio_path:
            return None
        
        # 获取歌词
        try:
            r_lyric = requests.get(f"https://163api.qijieya.cn/lyric?id={track_id}", timeout=10)
            if r_lyric.status_code == 200:
                lyric_data = r_lyric.json()
                lyric = lyric_data.get("lrc", {}).get("lyric", "") or lyric_data.get("lyric", "")
            else:
                lyric = ""
        except Exception as e:
            print(f"歌词获取失败: {str(e)}")
            lyric = ""
        
        # 设置标签
        self.set_audio_tags(audio_path, track_info, cover_path,lyric)
        
        print(f"下载完成: {track_info['name']} - {track_info['artist']}")
        print(f"文件保存到: {audio_path}")
        
        t1=threading.Thread(target=self.get_storage_size)
        t1.start()
        t2=threading.Thread(target=self.remove_cover,args=(cover_path,))
        t2.start()
        return audio_path, lyric
