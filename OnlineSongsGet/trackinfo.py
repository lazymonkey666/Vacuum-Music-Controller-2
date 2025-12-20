import requests
class TrackInfo():
    def __init__(self):
        self.trackinfo_url="https://163api.qijieya.cn/playlist/track/all"
        self.vip_check="https://music.163.com/#/song?id="
    def get_trackinfo(self,trackid:int):
        params={
            "id":trackid
        }
        response=requests.get(self.trackinfo_url,params=params)
        song_ids=[]
        song_names=[]
        if response.status_code == 200:
            data = response.json()
            if data.get("code") == 200 and "songs" in data:
                result_list = []  # 用于存储最终结果的列表
                for song in data["songs"]:
                    song_id = song["id"]
                    song_name = song["name"]
                    
                    # 构建歌手名字字符串，用 & 连接
                    song_artists = []
                    for artist in song["ar"]:
                        song_artists.append(artist["name"])
                    artist_string = " & ".join(song_artists)
                    
                    # 为单首歌创建格式化字符串
                    
                    song_final = f"{song_name} - {artist_string}"
                    
                    
                    # 将 (id, 格式化字符串) 作为元组添加到结果列表
                    result_list.append((song_id, song_final))
                
                # 返回包含所有歌曲信息的列表
                return result_list
            else:
                print(f"API未返回有效数据。Code: {data.get('code')}")
                return None
        else:
            print(f"HTTP请求失败，状态码: {response.status_code}")
            return None
